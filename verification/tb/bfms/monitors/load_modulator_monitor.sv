/***********************************************************************
        File: load_modulator_monitor.sv
 Description: A monitor for the output to the load modulator
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

package load_modulator_monitor_pkg;

    // This monitor produces TxBitTransactions
    // we could create a new transaction for the actual outputs, but
    // I don't think we ever want to look at the subcarrier and'd with the manchester
    // encoded data. So we just convert that here to bits.

    class LoadModulatorMonitor
    #(
        // The iface must contain: lm
        // it must also be virtual.
        type IfaceType = virtual load_modulator_iface,
        // We expect the transaction to extend TxBitTransaction
        type TransType = tx_bit_transaction_pkg::TxBitTransaction
    )
    extends monitor_pkg::Monitor
    #(
        .IfaceType  (IfaceType),
        .TransType  (TransType)
    );

        function new (IfaceType _vif);
            super.new(_vif);
        endfunction

        // The load modulator output is the manchester encoded data AND'd with the subcarrier
        // Manchester encoding:
        //      0 -> 64 bits of 0, 64 bits of 1
        //      1 -> 64 bits of 1, 64 bits of 0
        // The subcarrier has frequency Fc / 16, so it toggles every 8 ticks.
        // The subcarrier starts with a rising edge in sync with the Manchester encoded data.
        // So AND'ing the two together gives:
        //      0 -> 00000000 00000000
        //           00000000 00000000
        //           00000000 00000000
        //           00000000 00000000
        //           11111111 00000000
        //           11111111 00000000
        //           11111111 00000000
        //           11111111 00000000
        //
        //      1 -> 11111111 00000000
        //           11111111 00000000
        //           11111111 00000000
        //           11111111 00000000
        //           00000000 00000000
        //           00000000 00000000
        //           00000000 00000000
        //           00000000 00000000
        //
        // Finally frames start with a SOC which is a logical 1, and idle is always low.
        // So we can detect start of frame by waiting for a rising edge.
        // and we can detect idle by waiting for 128 ticks of 0s.
        localparam logic [127:0] LM_IDLE = '0;
        localparam logic [127:0] LM_BIT_0 = {64'b0, {4{8'hFF, 8'h00}}};
        localparam logic [127:0] LM_BIT_1 = {{4{8'hFF, 8'h00}}, 64'b0};

        virtual protected task wait_for_frame_start(TransType trans);
            // the load modulator signal is idle low
            // SOC is a '1', the manchester encoding of that is high then low
            // so wait for lm to assert
            wait (vif.lm) begin end

            // sync to the clk edge
            @(posedge vif.clk) begin end
        endtask

        virtual protected task sample_data_bit(output logic received, output logic res, output logic idle);
            automatic logic [127:0] read;

            // assume not idle and not an error
            res     = 1'b1;
            idle    = 1'b0;

            repeat (128) begin
                read = {read[126:0], vif.lm};
                @(posedge vif.clk) begin end
            end

            if (read == LM_BIT_0) begin
                received = 1'b0;
            end
            else if (read == LM_BIT_1) begin
                received = 1'b1;
            end
            else if (read == LM_IDLE) begin
                idle = 1'b1;
            end
            else begin
                // error
                $error("Received invalid bit pattern on the load modulator output signal: %b", read);
                res = 1'b0;
            end
        endtask

        virtual protected task sample_data_bit_trans(TransType trans, output logic res, output logic idle);
            logic received;
            sample_data_bit(received, res, idle);

            // if it was an error, then we already called $error in sample_data_bit
            // so it could be idle, 0, or 1.
            // if it's idle we're done, otherwise push the bit to the transaction
            if (res && !idle) begin
                trans.push_back(received);
            end
        endtask

        virtual protected task sample_start_bit(TransType trans, output logic res);
            logic received;
            logic idle;
            sample_data_bit(received, res, idle);

            // if it was an error, then we already called $error in sample_data_bit
            // If it was valid, it had to be a logical 1 (SOC), because we only get here after calling
            // wait_for_frame_start which means the first tick was a 1, which can only be a logical 1.
        endtask

        // only called on errors (not to be mixed up with Monitor::wait_for_idle)
        virtual protected task wait_for_lm_idle;
            automatic logic [127:0] read = '1;

            forever begin
                read = {read[126:0], vif.lm};
                if (read == LM_IDLE) begin
                    // done
                    return;
                end

                @(posedge vif.clk) begin end
            end
        endtask

        virtual protected task process(output TransType trans, output logic res);
            res     = 1'b0; // no valid result yet
            idle    = 1'b1; // currently idle, waiting for a frame
            trans   = new();

            // wait for a frame to start
            wait_for_frame_start(trans);

            idle = 1'b0;    // no longer idle

            // read in the start bit
            sample_start_bit(trans, res);

            // sample the data, 128 ticks at a time
            while (res && !idle) begin
                // res is 1'b1 if the next 128 ticks are a valid '1', '0' or idle.
                // idle gets set if we receive a full bit time of 0s.
                // res is 1'b0 if we receive an unexpected sequence of bits
                sample_data_bit_trans(trans, res, idle);
            end

            if (!idle) begin
                // we are here because of an error
                // wait for us to be idle before we return
                wait_for_lm_idle;
                idle = 1'b1;
            end
        endtask
    endclass

endpackage
