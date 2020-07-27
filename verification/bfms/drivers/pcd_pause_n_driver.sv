/***********************************************************************
        File: pcd_pause_n_driver.sv
 Description: A driver to drive the pause_n signal coming from the PCD
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

// Note: This is mimicing the PCD's output. To correctly simulate the input to this digital
//       part of the ISO/IEC 14443A IP core, this driver must be used alongside the clk_recovery
//       and pause_detect modules, which simulates recovering the clock from the carrier wave
//       (clock stops during pauses) and simulates the propagation delay of the pause_n signal
//       in the analogue block (so that the pause_n signal is not synchronous to the PICC's clock).

//       This driver and the above modules and the pcd_pause_n_iface are encapsulated together
//       in the analogue_sim module for ease of use

package pcd_pause_n_driver_pkg;

    class PCDPauseNDriver
    extends driver_pkg::Driver
    #(
        .IfaceType  (virtual pcd_pause_n_iface),
        .TransType  (pcd_pause_n_transaction_pkg::PCDPauseNTransaction)
    );

        // timing
        protected int bit_ticks;
        protected int pause_ticks;
        protected int sequence_x_pause_start_offset_ticks;
        protected int sequence_z_pause_start_offset_ticks;
        protected int ticks_after_transaction;

        // some debug signals we can see in the GUI if we need to debug
        protected logic first_tick_in_bit;
        protected int   tick_count;

        // flags
        protected logic add_error;

        function new (IfaceType _vif,
                      int _bit_ticks                            = 128,
                      int _pause_ticks                          = 32,
                      int _sequence_x_pause_start_offset_ticks  = 64,
                      int _sequence_z_pause_start_offset_ticks  = 0,
                      int _ticks_after_transaction              = 256); // two bit times
            super.new(_vif);

            vif.pcd_pause_n = 1'b1; // idle

            bit_ticks                           = _bit_ticks;
            pause_ticks                         = _pause_ticks;
            sequence_x_pause_start_offset_ticks = _sequence_x_pause_start_offset_ticks;
            sequence_z_pause_start_offset_ticks = _sequence_z_pause_start_offset_ticks;
            ticks_after_transaction             = _ticks_after_transaction;

            tick_count          = 0;
            first_tick_in_bit   = 1'b0;
            add_error           = 1'b0;
        endfunction

        // Only call this when the driver is not transmitting
        virtual function void set_bit_ticks (int _bit_ticks);
            bit_ticks = _bit_ticks;
        endfunction

        // Only call this when the driver is not transmitting
        virtual function void set_pause_ticks (int _pause_ticks);
            pause_ticks = _pause_ticks;
        endfunction

        virtual protected task do_pause;
            vif.pcd_pause_n <= 1'b0;
            repeat (pause_ticks) @(posedge vif.clk) begin end
            vif.pcd_pause_n <= 1'b1;
        endtask

        virtual protected task send_sequence_x;
            repeat (sequence_x_pause_start_offset_ticks) @(posedge vif.clk) begin end
            do_pause;
        endtask

        virtual protected task send_sequence_z;
            repeat (sequence_z_pause_start_offset_ticks) @(posedge vif.clk) begin end
            do_pause;
        endtask

        virtual protected task send_sequence_y;
            // do nothing
        endtask

        virtual protected task send_sequence_error;
            // we can guarantee an error by having a pause at the start of the bit time (sequence Z)
            // and then a short time later sending a second pause.
            // An error could be detected on the first pause if the previous sequence was an X,
            // since X -> Z is an error. Otherwise/ sequence_decode detects an error if two
            // pauses are < 64 PICC clk ticks apar. We need to leave enough of a gap so that
            // the PICC detects them as two separate pauses. Using 48 ticks. This could fail
            // if the analogue block has huge delays but I don't think there's much point in
            // testing with delays of more than a few ticks.
            do_pause;
            repeat(48) @(posedge vif.clk) begin end
            do_pause;
        endtask

        virtual protected task send_elem (TransType trans, int idx);
            automatic ISO14443A_pkg::PCDBitSequence seq = trans.data[idx];

            // fork-join_none to make the sending of the pause non-blocking
            // this means pauses can run over into the start of the next bit time
            // as would happen with a sequence X (sequence_x_pause_start_offset_ticks == 64)
            // and pause_ticks > 64, etc...
            fork
                begin
                    case (seq)
                        ISO14443A_pkg::PCDBitSequence_X:        send_sequence_x;
                        ISO14443A_pkg::PCDBitSequence_Y:        send_sequence_y;
                        ISO14443A_pkg::PCDBitSequence_Z:        send_sequence_z;
                        ISO14443A_pkg::PCDBitSequence_ERROR:    send_sequence_error;
                    endcase
                end
            join_none

            // wait one bit time before returning, the above process may or may not have
            // completed by that time.
            repeat (bit_ticks) @(posedge vif.clk) begin end
        endtask

        virtual protected task process(TransType trans);
            //$display("sending %p", trans);

            tick_count          = 0;
            first_tick_in_bit   = 0;

            if (add_error) begin
                // don't mess with the first sequence (SOC)
                automatic int idx = $urandom_range(1, trans.size() - 1);
                trans.data[idx] = ISO14443A_pkg::PCDBitSequence_ERROR;
            end

            // sync to clk edge
            @(posedge vif.clk) begin end

            // we surround the main fork - join_any disable fork; with another fork
            // this is so that the disable fork; only disables this fork, and not
            // any parent forks (such as the one in start())
            // see: https://stackoverflow.com/a/14481391
            fork
                begin
                    fork
                        // process 1 - send the data
                        begin
                            foreach (trans.data[i]) begin
                                send_elem(trans, i);
                            end
                            repeat (ticks_after_transaction) @(posedge vif.clk) begin end
                        end

                        // process 2 - produce debug signals (never exits)
                        begin
                            forever begin
                                forever begin
                                    first_tick_in_bit = (tick_count == 0);
                                    @(posedge vif.clk) begin end
                                    tick_count = (tick_count + 1) % bit_ticks;
                                end
                            end
                        end
                    join_any

                    disable fork;   // disable the debug signal process
                end
            join
        endtask

        // This doesn't account for any delays in the analogue block
        // and is in PCD clock ticks
        virtual function int calculate_send_time(TransType trans);
            return (trans.data.size() * bit_ticks) + ticks_after_transaction + 1;
        endfunction

        virtual function void set_add_error(logic _add_error);
            add_error = _add_error;
        endfunction

        virtual function logic get_add_error;
            return add_error;
        endfunction
    endclass

endpackage
