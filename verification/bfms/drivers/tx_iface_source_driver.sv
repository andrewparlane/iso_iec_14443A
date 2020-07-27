/***********************************************************************
        File: tx_iface_source_driver.sv
 Description: A generic driver for all Tx interfaces acting as the source
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

package tx_iface_source_driver_pkg;

    // The tx_iface has:
    //  data                - driven by the source (us)
    //  data_valid          - driven by the source (us)
    //  req                 - driven by the sink

    // When BY_BYTE is not set, we also have:
    //  last_bit_in_byte    - driven by the source (us)

    // When BY_BYTE is set, we also have:
    //  data_bits           - driven by the source (us)

    class TxIfaceSourceDriver
    #(
        // The iface must contain clk, data, data_valid
        // it must also be virtual. E.g. "virtual tx_interface #(.BY_BYTE(0))"
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

        // enforce idle time before sending the next transaction
        // this should be set to ensure that the sink detects that there is no more data to send
        protected int idle_ticks_after_transaction;

        // how long to wait for the next request signal (not the first)
        protected int req_timeout;

        // how long to wait for the first request signal
        // this is useful with the FDT, which may have a long delay before
        // the first req pulse but other req pulses come more often after.
        protected int first_req_timeout;

        // flags
        protected logic timedout;
        protected logic enable_timeout_errors;

        function new (IfaceType _vif,
                      int _idle_ticks_after_transaction = 32,
                      int _req_timeout                  = 32,
                      int _first_req_timeout            = _req_timeout);
            super.new(_vif);

            vif.data_valid  = 1'b0;

            idle_ticks_after_transaction    = _idle_ticks_after_transaction;
            req_timeout                     = _req_timeout;
            first_req_timeout               = _first_req_timeout;
            enable_timeout_errors           = 1'b1;
        endfunction

        virtual protected task send_data_elem(TransType trans, int idx);
            vif.data        <= trans.data[idx];
            vif.data_valid  <= 1'b1;
        endtask

        virtual protected task wait_for_req(TransType trans, int idx);
            automatic int timeout = (idx == 0) ? first_req_timeout
                                               : req_timeout;

            // we surround the main fork - join_any disable fork; with another fork
            // this is so that the disable fork; only disables this fork, and not
            // any parent forks (such as the one in start())
            // see: https://stackoverflow.com/a/14481391
            fork
                begin
                    fork
                        // process 1 - wait for req
                        begin
                            //$display("process 1 - wait for req");
                            wait (vif.req) begin end
                            // sync to clk edge again
                            @(posedge vif.clk) begin end
                            //$display("process 1 - wait for req - done at %t", $time);
                        end

                        // process 2 - timeout
                        begin
                            //$display("process 2 - timeout");
                            if (timeout > 0) begin
                                repeat (timeout) @(posedge vif.clk) begin end
                            end
                            else begin
                                forever @(posedge vif.clk) begin end
                            end
                            //$display("process 2 - timeout - done at %t", $time);
                            if (enable_timeout_errors) begin
                                $error("wait_for_req timed out after %d ticks", timeout);
                            end
                            timedout = 1'b1;
                        end
                    join_any

                    disable fork;   // disable the other process
                end
            join
        endtask

        virtual protected task send_data(TransType trans);
            foreach (trans.data[i]) begin
                // update data and set data_valid (if it wasn't already)
                send_data_elem(trans, i);

                // to ensure req is not still set
                @(posedge vif.clk) begin end

                // wait for the next req pulse
                wait_for_req(trans, i);

                if (timedout) begin
                    break;
                end

                // we could add a delay here to simulate delays between req and the data
                // being updated.
            end

            // nothing more to send / we timed out
            vif.data_valid <= 1'b0;
        endtask

        virtual protected task process(TransType trans);
            //$display("sending %p", trans);

            // sync to clk edge
            @(posedge vif.clk) begin end

            timedout = 1'b0;
            send_data(trans);

            repeat (idle_ticks_after_transaction) @(posedge vif.clk) begin end
        endtask

        // send time is dependent on the sink pulsing the req pulse
        // since the process() task will timeout in wait_for_req() we should wait
        // for either that to happen or the transaction to finish. Hence we return -1
        // which means Driver::wait_for_idle() should wait forever, or at least until
        // process() finishes either due to a tiemout or successfull completion
        virtual function int calculate_send_time(TransType trans);
            return -1;
        endfunction

        virtual function void set_enable_timeout_errors(logic _enable_timeout_errors);
            enable_timeout_errors = _enable_timeout_errors;
        endfunction

    endclass

endpackage
