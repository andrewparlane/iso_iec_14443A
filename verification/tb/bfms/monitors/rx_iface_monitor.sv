/***********************************************************************
        File: rx_iface_monitor.sv
 Description: A generic monitor for all Rx interfaces
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

package rx_iface_monitor_pkg;

    // The rx_iface has:
    //  SOF
    //  EOP
    //  data
    //  data_valid
    //  error

    // When BY_BYTE is set, we also have:
    //  data_bits

    class RxIfaceMonitor
    #(
        // The iface must contain clk, soc, eoc, data, data_valid, error
        // it must also be virtual. E.g. "virtual rx_interface #(.BY_BYTE(0))"
        type IfaceType,
        // We expect the transaction to extend QueueTransaction
        // The ElemType should be the same type as the iface's data signal.
        // It should also contain error_detected
        type TransType
    )
    extends monitor_pkg::Monitor
    #(
        .IfaceType  (IfaceType),
        .TransType  (TransType)
    );
        typedef enum
        {
            ResultCode_OK,
            ResultCode_ERROR,
            ResultCode_TRANSACTION_COMPLETE
        } ResultCode;

        function new (IfaceType _vif);
            super.new(_vif);
        endfunction

        virtual protected function event_detected;
            return vif.soc || vif.eoc || vif.error || vif.data_valid;
        endfunction

        virtual protected task wait_for_event;
            forever begin
                if (event_detected) begin
                    //$display("event detected: %s at time %t", vif.to_string(), $time);
                    break;
                end
                @(posedge vif.clk) begin end
            end
        endtask

        // if overridden, must deassert the idle flag on SOC
        virtual protected function ResultCode handle_event(TransType trans);
            if (idle) begin
                // only valid event is a SOC
                if (vif.eoc || vif.error || vif.data_valid || !vif.soc) begin
                    $error("Monitor: iface currently %s, when expecting SOC", vif.to_string());
                    return ResultCode_ERROR;
                end

                // yay SOC, we're no longer idle
                //$display("SOC detected");
                idle = 1'b0;
            end
            else begin
                if (vif.soc || (vif.data_valid && vif.error)) begin
                    // can't get a SOC whilst we're already in a frame
                    // and data_valid isn't allowed at the same time as error
                    $error("Monitor: iface currently %s, when not idle", vif.to_string());
                    return ResultCode_ERROR;
                end

                if (vif.data_valid) begin
                    trans.push_back(vif.data);
                end

                if (vif.error) begin
                    trans.error = 1'b1;
                end

                if (vif.eoc) begin
                    return ResultCode_TRANSACTION_COMPLETE;
                end
            end

            return ResultCode_OK;
        endfunction

        virtual protected task process(output TransType trans, output logic res);
            res     = 1'b0; // no valid result yet
            idle    = 1'b1; // currently idle, waiting for a frame
            trans   = new();

            forever begin
                ResultCode handle_event_res;
                wait_for_event;
                handle_event_res = handle_event(trans);
                @(posedge vif.clk) begin end    // so we don't detect the same event on the next pass
                if (handle_event_res != ResultCode_OK) begin
                    res     = (handle_event_res == ResultCode_TRANSACTION_COMPLETE);
                    idle    = 1'b1;
                    return;
                end
            end
        endtask
    endclass

endpackage
