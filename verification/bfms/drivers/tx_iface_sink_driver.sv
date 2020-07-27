/***********************************************************************
        File: tx_iface_sink_driver.sv
 Description: A generic driver for all Tx interfaces acting as the sink
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

package tx_iface_sink_driver_pkg;

    // The tx_iface has:
    //  data                - driven by the source
    //  data_valid          - driven by the source
    //  req                 - driven by the sink (us)

    // When BY_BYTE is set, we also have:
    //  data_bits           - driven by the source
    //  last_bit_in_byte    - driven by the source

    // Note: This class doesn't extend the generic Driver base class, since
    //       it doesn't really work in the same way, there's no Transaction Queue to send
    //       all we do is wait for data_valid to assert and then periodically pulse req
    //       until data_valid is no longer asserted
    //       It could make sense to turn this into a monitor instead, except a monitor
    //       shouldn't drive any signals on the bus.

    class TxIfaceSinkDriver
    #(
        // The iface must contain clk, data_valid, req
        // it must also be virtual. E.g. "virtual tx_interface #(.BY_BYTE(0))"
        type IfaceType
    );

        // Our virtual iface
        IfaceType vif;

        // timing
        protected int ticks_before_first_req;
        protected int ticks_between_reqs;   // must be >= 1 or req will be set through the entire frame

        // constructor
        function new (IfaceType _vif,
                      int _ticks_before_first_req   = 16,
                      int _ticks_between_reqs       = 16);
            vif = _vif;

            vif.req = 1'b0;

            ticks_before_first_req  = _ticks_before_first_req;
            ticks_between_reqs      = _ticks_between_reqs;
        endfunction

        // Call this to start the run thread
        virtual task start;
            fork
                begin
                    run_thread;
                end
            join_none
        endtask

        // The run_thread, this should never exit
        virtual protected task run_thread;
            forever begin
                //$display("Sink Driver: wait for data_valid");
                // wait for data_valid to be set
                wait (vif.data_valid) begin end

                // wait a bit before issuing the first req
                //$display("Sink Driver: wait for ticks_before_first_req %d", ticks_before_first_req);
                repeat (ticks_before_first_req) @(posedge vif.clk) begin end

                while (vif.data_valid) begin
                    // assert req for one tick
                    //$display("Sink Driver: asserting req");
                    vif.req <= 1'b1;
                    @(posedge vif.clk)
                    vif.req <= 1'b0;

                    // wait a bit before issuing the next req
                    //$display("Sink Driver: wait for ticks_between_reqs %d", ticks_between_reqs);
                    repeat (ticks_between_reqs) @(posedge vif.clk) begin end
                end
            end
        endtask

    endclass

    // alias for bit interface
    class TxBitIfaceSinkDriver
    extends TxIfaceSinkDriver
    #(
        .IfaceType (virtual tx_interface #(.BY_BYTE(0)))
    );

        // constructor
        function new (IfaceType _vif,
                      int _ticks_before_first_req   = 16,
                      int _ticks_between_reqs       = 16);
            super.new(_vif, _ticks_before_first_req, _ticks_between_reqs);
        endfunction

    endclass

    // alias for byte interface
    class TxByteIfaceSinkDriver
    extends TxIfaceSinkDriver
    #(
        .IfaceType (virtual tx_interface #(.BY_BYTE(1)))
    );
        // constructor
        function new (IfaceType _vif,
                      int _ticks_before_first_req   = 16,
                      int _ticks_between_reqs       = 16);
            super.new(_vif, _ticks_before_first_req, _ticks_between_reqs);
        endfunction
    endclass

endpackage
