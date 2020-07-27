/***********************************************************************
        File: rx_iface_driver.sv
 Description: A generic driver for all Rx interfaces
      Author: Andrew Parlane
**********************************************************************/

/*
 * This file is part of https://github.com/andrewparlane/iso_iec_14443A
 * Copyright (c) 2020 Andrew Parlane.
 *
 * This is free software: you can redistribute it and/or modify it under
 * the terms of the GNU General Public License as published by the Free
 * Software Foundation, version 3.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this code. If not, see <http://www.gnu.org/licenses/>.
 */

`timescale 1ps/1ps

package rx_iface_driver_pkg;

    // The rx_iface has:
    //  SOF
    //  EOP
    //  data
    //  data_valid
    //  error

    // When BY_BYTE is set, we also have:
    //  data_bits

    class RxIfaceDriver
    #(
        // The iface must contain clk, soc, eoc, data, data_valid, error
        // it must also be virtual. E.g. "virtual rx_interface #(.BY_BYTE(0))"
        type IfaceType,
        // We expect the transaction to contain data [$],
        // it should be of the same width as data in the iface
        type TransType
    )
    extends driver_pkg::Driver
    #(
        .IfaceType  (IfaceType),
        .TransType  (TransType)
    );

        // some delays
        protected int   ticks_after_soc;
        protected int   ticks_after_data;
        protected int   ticks_after_transaction;

        // flags
        protected logic add_error;
        protected int   error_location;
        protected logic error_sent;

        function new (IfaceType _vif, int _ticks_after_soc=5, int _ticks_after_data=5, int _ticks_after_transaction=5);
            super.new(_vif);

            vif.soc         = 1'b0;
            vif.eoc         = 1'b0;
            vif.error       = 1'b0;
            vif.data_valid  = 1'b0;

            ticks_after_soc             = _ticks_after_soc;
            ticks_after_data            = _ticks_after_data;
            ticks_after_transaction     = _ticks_after_transaction;

            add_error = 1'b0;
        endfunction

        // takes ticks_after_soc + 2 ticks
        virtual protected task send_soc(TransType trans);
            // sync to a clock edge
            @(posedge vif.clk) begin end

            // SOC
            vif.soc <= 1'd1;
            @(posedge vif.clk)
            vif.soc <= 1'd0;

            repeat (ticks_after_soc) @(posedge vif.clk) begin end
        endtask

        // takes 1 tick
        virtual protected task send_body_element(TransType trans, int idx);
            vif.data        <= trans.data[idx];
            vif.data_valid  <= 1'b1;
            @(posedge vif.clk)
            vif.data_valid  <= 1'b0;
        endtask

        // takes 1 tick
        virtual protected task send_error(TransType trans);
            vif.error <= 1'b1;
            @(posedge vif.clk)
            vif.error <= 1'b0;
            error_sent = 1'b1;
        endtask

        // takes at most (ticks_after_data + 1) * (trans.data.size() + add_error) ticks
        virtual protected task send_body(TransType trans);
            foreach (trans.data[i]) begin
                // error before this data element?
                if (add_error && (error_location == i)) begin
                    send_error(trans);
                    repeat (ticks_after_data) @(posedge vif.clk) begin end
                end
                send_body_element(trans, i);
                repeat (ticks_after_data) @(posedge vif.clk) begin end
            end

            // error before EOC?
            if (add_error && (error_location == trans.data.size())) begin
                send_error(trans);
                repeat (ticks_after_data) @(posedge vif.clk) begin end
            end
        endtask

        // takes 1 ticks
        virtual protected task send_eoc(TransType trans);
            // error on EOC?
            if (add_error && (error_location == (trans.data.size() + 1))) begin
                vif.error       <= 1'b1;
                error_sent      = 1'b1;

                // data can be sent on the EOC (by child classes),
                // so make sure data_valid is low as we can't have
                // valid data and an error at the same time
                vif.data_valid  <= 1'b0;
            end

            // eoc
            vif.eoc         <= 1'b1;
            @(posedge vif.clk)
            vif.eoc         <= 1'b0;
            vif.error       <= 1'b0;
        endtask

        virtual protected task process(TransType trans);
            //$display("sending %p", trans);

            // the error can be added either before a data element, before the EOC
            // or on the EOC. So that's trans.data.size() + 2 locations.
            // It's only added if add_error is set
            error_location  = $urandom_range(trans.data.size() + 1);
            error_sent      = 0;
            //if (add_error) $display("error_location: %d, data.size %d", error_location, trans.data.size());

            send_soc(trans);
            send_body(trans);
            send_eoc(trans);

            errorSentAsExpected: assert (add_error == error_sent) else $error("add_error %b != error_sent %b", add_error, error_sent);

            repeat (ticks_after_transaction) @(posedge vif.clk) begin end
        endtask

        // don't rely on this to be perfect, but it can be used as a startpoint for wait_for_idle()
        virtual function int calculate_send_time(TransType trans);
            return ticks_after_soc +
                   ((ticks_after_data + 1) * (trans.data.size()) + add_error) +
                   ticks_after_transaction + 4;
        endfunction

        virtual function void set_add_error(logic _add_error);
            add_error = _add_error;
        endfunction

        virtual function logic get_add_error;
            return add_error;
        endfunction

    endclass

endpackage
