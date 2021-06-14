/***********************************************************************
        File: clk_recovery.sv
 Description: Simulates clock recovery from the carrier wave
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

// This module simulates the behaviour of the ISO/IEC 14443A analogue IP core
// for use with simulations.
// It takes the pcd_clk and the pcd_pause_n signal, and produces the picc_clk
// The variables in here should be tweaked carefully to mimic the
// actual analogue IP core as closely as possible.

// Variables:
//      clock_stops_after_ps        - the clk output stops a number of ps after the "PCD" decides to send a pause.
//      clock_starts_after_ps       - it starts again a number of ps after the "PCD" decides to stop sending the pause.

module clk_recovery
(
    input           pcd_clk,
    input           pcd_pause_n,

    output logic    picc_clk    // Note: the clk stops during pauses (see clock_stops_after_ps and clock_starts_after_ps)
);

    // ------------------------------------------------------------------------
    // Comments about how this code works
    // ------------------------------------------------------------------------

    // When the PCD wants to send data it uses on-off-keying (OOK) to send a "pause frame"
    // Meaning the PICC detects the carrier wave reducing to < 5% of it's former value,
    // for a period of time.

    // Since the PICC generates it's clock based off the carrier wave, the PICC's clock
    // halts during pause frames.

    // When the clock halts / starts again depends on the analogue part of the
    // PICC implementation. I simulate this using the variables:
    //      The clock stops clock_stops_after_ps ps after pcd_pause_n asserts.
    //      The clock starts again clock_starts_after_ps ps after pcd_pause_n deasserts
    // These variables must be set to correctly emulate the analogue block.
    // Preferably the final verification will be run numerous times with these variables
    // randomised within the expected range due to PVT.

    // ------------------------------------------------------------------------
    // Variables
    // ------------------------------------------------------------------------

    // I currently have no data on how long this takes. It depends on the switching point
    // of the inverters in the clock generator, and how long it takes the PCD's output to
    // reach that point. Picking values semi at random.
    // TODO: set these appropriately
    logic   clock_stops             = 1'b1;
    int clock_stops_after_ps        = 500 * 1000; // 500 ns
    int clock_starts_after_ps       = 100 * 1000; // 100 ns

    // ------------------------------------------------------------------------
    // pause_n detector
    // ------------------------------------------------------------------------

    // We perform delayed assignments on the stop_clk signal
    logic stop_clk;
    always_comb begin
        if (!pcd_pause_n) begin
            if (clock_stops) begin
                // pcd_pause_n asserted
                stop_clk <= #clock_stops_after_ps 1'b1;
            end
        end
        else begin
            // pcd_pause_n deasserted
            stop_clk <= #clock_starts_after_ps 1'b0;
        end
    end

    // generate the PICC's clock
    // Note: this clock can be in phase to the pcd_clk or 180 degrees out of phase.
    //       and it can change between them, depending on when the clock stops
    //       and starts. This matches the analogue implementation of the clock
    //       recovery block.
    logic picc_clk_internal = 1'b0; // use a temp var so we can initialise it.
    always_ff @(posedge pcd_clk, negedge pcd_clk) begin
        if (!stop_clk) begin
            picc_clk_internal <= !picc_clk_internal;
        end
    end
    assign picc_clk = picc_clk_internal;

    // ------------------------------------------------------------------------
    // Variable get / set functions
    // ------------------------------------------------------------------------

    function void set_params(logic new_clock_stops,
                             int new_clock_stops_after_ps,
                             int new_clock_starts_after_ps);
        clock_stops                 = new_clock_stops;
        clock_stops_after_ps        = new_clock_stops_after_ps;
        clock_starts_after_ps       = new_clock_starts_after_ps;
    endfunction

endmodule
