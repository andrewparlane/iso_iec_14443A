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

    // The sequence_decode module counts the number of ticks between rising edges of pause_n
    // to determine what the next sequence is. Since the clock stops for some number of ticks
    // during pauses, we have to take that into account. The sequence_decode is designed to
    // support as wide a range of options as possible. The supported range of dropped clock ticks
    // is -3 to 58. Or in other terms, -6 to 116 edges. The negative value here indicates that
    // if the clock doesn't stop at all, everything will work fine. -3 Also allows for up to 3 ticks
    // of jitter when detecting the rising edge of the pause even when the clock doesn't stop at all.
    // To support a bit of jitter on the other side of the range, I reccomend ensuring the clock stops
    // for no more than 110 edges (55 ticks).
    //
    // The number of dropped edges is determined by:
    //      missing_edges = 2*pcd_pause_len -
    //                      $floor(2.0*clock_stops_after_ps/CLOCK_PERIOD_PS) +
    //                      $floor(2.0*clock_starts_after_ps/CLOCK_PERIOD_PS);
    //
    // Additionally the clock must start again before the start of the next pause. The worst case
    // for that is a sequence Z -> sequence X, which is treated as an error. We do however want
    // to detect this as an error, and so we require clock_stops_after_ps < 64 - pcd_pause_len
    // which in it's worst case is 64 - 41 = 23 ticks which with the min permited period of
    // 13.56MHz - 7KHz, is 1.697us.
    //
    // In sumarry the requirements are:
    //      clock_starts_after_ps < 1.6us
    //      the clock stopping must cause us to miss at most 110 edegs.
    //
    // The AFE must ensure that this requirement is always met for all valid inputs
    // from the PCD in terms of frequency and rise / fall times.
    // My sequence_decode_tb shows that sequence_decode will work as long as these requiremnts
    // are met.

    // ------------------------------------------------------------------------
    // Variables
    // ------------------------------------------------------------------------

    // The actual value for these depends on the AFE which doesn't exist for our process yet,
    // and the characteristics of the PCD's pause signal (rise and fall times).
    // The values I've chosen come from a SPICE simulation of the AFE that Fabricio
    // designed for a different fabrication process, using a typical PCD pause.
    // (see ISO/IEC 14443-2A:2016 figure 3 and table 4).
    //  t1 (pcd_pause_len) = 33/fc  = 2.43 us
    //  t2                 = 32/fc  = 2.36 us
    //  t3                 =  6/fc  = 0.44 us
    logic   clock_stops             = 1'b1;
    int     clock_stops_after_ps    =  56 * 1000; // 56 ns
    int     clock_starts_after_ps   = 145 * 1000; // 145 ns

    // These values lead to 68 missing edges or 34 missing ticks.

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
