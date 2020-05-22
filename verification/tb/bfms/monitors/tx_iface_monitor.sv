/***********************************************************************
        File: tx_iface_monitor.sv
 Description: A generic monitor for all Tx interfaces
      Author: Andrew Parlane
**********************************************************************/

/*
 * This file is part of https://github.com/andrewparlane/fiuba_thesis/blob/master/LICENSE
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

package tx_iface_monitor_pkg;

    // The tx_iface has:
    //  data                - driven by the source
    //  data_valid          - driven by the source
    //  req                 - driven by the sink

    // When BY_BYTE is not set, we also have:
    //  last_bit_in_byte    - driven by the source

    // When BY_BYTE is set, we also have:
    //  data_bits           - driven by the source

    class TxIfaceMonitor
    #(
        // The iface must contain data, data_valid, req
        // it must also be virtual. E.g. "virtual tx_interface #(.BY_BYTE(0))"
        type IfaceType,
        // We expect the transaction to extend QueueTransaction
        // The ElemType should be the same type as the iface's data signal
        type TransType
    )
    extends monitor_pkg::Monitor
    #(
        .IfaceType  (IfaceType),
        .TransType  (TransType)
    );

        function new (IfaceType _vif);
            super.new(_vif);
        endfunction

        virtual protected task wait_for_data_valid;
            wait (vif.data_valid) begin end
            // sync to clock edge
            @(posedge vif.clk) begin end
        endtask

        virtual protected function void sample_data(TransType trans);
            trans.push_back(vif.data);
        endfunction

        virtual protected task process(output TransType trans, output logic res);
            res     = 1'b0; // no valid result yet
            idle    = 1'b1; // currently idle, waiting for a frame
            trans   = new();

            forever begin
                // wait for data_valid to assert, indicating a transaction is starting
                wait_for_data_valid;

                idle = 1'b0;    // no longer idle

                forever begin
                    // we sample data on the req pulse because that is when it must be valid
                    // if the data is stlil not correct by that point, then it's too late
                    wait (vif.req | !vif.data_valid) begin end
                    // sync to clock edge
                    @(posedge vif.clk) begin end

                    // if data_valid fell, then we have reached the end of the frame
                    if (!vif.data_valid) begin
                        res = 1'b1;
                        idle = 1'b1;
                        return;
                    end

                    // now we can sample the data
                    sample_data(trans);

                    // wait a tick for the req to clear
                    @(posedge vif.clk) begin end
                end
            end
        endtask
    endclass

endpackage
