/***********************************************************************
        File: pause_detect.sv
 Description: Simulates propagation delays in the analogue block
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
// It takes the pcd_pause_n signal, and produces the pause_n signal.
// The variables in here should be tweaked carefully to mimic the
// actual analogue IP core as closely as possible.

// Variables:
//      pause_n_asserts_after_ps    - the pause_n output asserts a number of ps after the "PCD" decides to send a pause.
//      pause_n_deasserts_after_ps  - it deasserts a number of ps after the "PCD" decides to stop sending the pause.

module pause_detect
(
    input           pcd_pause_n,
    output logic    pause_n_async   // Note: you can not rely on this to be synchronised to a clock edge
);

    // ------------------------------------------------------------------------
    // Comments about how this code works
    // ------------------------------------------------------------------------

    // When the PCD wants to send data it uses on-off-keying (OOK) to send a "pause frame"
    // Meaning the PICC detects the carrier wave reducing to < 5% of it's former value,
    // for a period of time.

    // The PICC contains a pause detector which asserts when it detects we are in a pause frame.

    // When the pause is detected / end of pause is detected, depends on the analogue part of
    // the PICC implementation. I simulate this using the variables:
    //      The pause_nasync signal asserts pause_n_asserts_after_ps ps pcd_pause_n asserts.
    //      The pause_nasync signal deasserts pause_n_deasserts_after_ps ps after pcd_pause_n deasserts.
    //
    // The sequence_decode module works via counting the number of ticks between the rising edge
    // of pauses. So the only requirement here is that the AFE has minimal jitter when detecting
    // the end of the pause (pause_n_deasserts_after_ps is constant when receiving the same PCD
    // input signal). Any jitter here should be accounted for when designing the clock recovery
    // block. See notes in clk_recovery.sv for more info.
    //
    // The fdt module aims to start the response transmission a precise number of ticks after the
    // last rising edge of the last pause of a frame. There are internal delays that have to be
    // taken into account, but we also have to consider the delays of the AFE. The standard says
    // that the actual FDT time must be between the specified number of ticks and the specified
    // number of ticks + 0.4 us (5.4 ticks). So we can send a little late but not too early,
    // meaning we should under-compensate for delays rather than over compensate. See fdt.sv for
    // more notes about this.
    // Here what matters is the time between the start of the end of the PCD's pause and the AFE's
    // pause_n signal deasserting, or in other words pause_n_deasserts_after_ps. The value of this
    // depends on the implementation of the AFE and the characteristics of the PCD's pause.
    // SPICE simulations of Fabricio's AFE shows values between 9ns and 602ns. Thiss is unfortunately
    // too large a range, since we only have 400ns of slack. Since we have to under-compensate
    // we need to use the minimum value of 9ns in our FDT calculations. Since that's well under
    // 1 tick, we can essentially assume the minimum here is 0ns. The maximum I set at 300ns in order
    // to give the remaining 100ns of slack as flexibilty elsewhere in the chain.
    //
    // Additionally the pause_n signal is passed through the pause_n_latch_and_synchroniser module,
    // so there's a delay of 3 rising edges (2 to 3 periods) there assuming the clock starts running
    // before pause_n deasserts. So this becomes another requirement:
    //      clock_starts_after_ps < pause_n_deasserts_after_ps.
    // We can compensate for 2 of those periods (minimum) with the FDT_TIMING_ADJUST parameter,
    // and the potential 3rd tick eats into the 100ns of our margin, leaving (with min frequency)
    // 26.2 ns.
    //
    // Other than that, the only other requirement is that pause_n_sychronised deasserts before the
    // start of the next pause. In the worst case that's the X->Z transition, with 64 - pcd_pause_len
    // ticks between the end of one pause (X) and the start of the next (Z). The synchroniser takes an
    // additional 3 ticks, so pause_n_deasserts_after_ps < (64 - pcd_pause_len - 3). Which in
    // the worst case (pcd_pause_len = 41) is pause_n_deasserts_after_ps < 20 ticks, which is much
    // higher than the 300ns requirement from above, so can safely be ignored
    //
    // In sumarry the requirements are:
    //      pause_n_deasserts_after_ps has minimal jitter for the same input pause signal
    //      pause_n_deasserts_after_ps < 300 ns
    //      clock_starts_after_ps < pause_n_deasserts_after_ps

    // ------------------------------------------------------------------------
    // Variables
    // ------------------------------------------------------------------------

    // The actual value for these depends on the AFE which doesn't exist for our process yet
    // and the characteristics of the PCD's pause. The values I've chosen come from a SPICE
    // simulation of the AFE that Fabricio designed for a different fabrication process,
    // using a typical PCD input signal (see ISO/IEC 14443-2A:2016 figure 3 and table 4):
    //  t1 (pcd_pause_len) = 33/fc
    //  t2                 = 32/fc
    //  t3                 =  6/fc
    int pause_n_asserts_after_ps    = 552 * 1000;  // 552 ns
    int pause_n_deasserts_after_ps  = 220 * 1000;  // 220 ns

    // ------------------------------------------------------------------------
    // pause_n_async detector
    // ------------------------------------------------------------------------

    // The PICC's pause_n_async signal asserts / deasserts some delay after the pcd_pause_n
    // signal, so just use the #(rise_delay, fall_delay) syntax of verilog.
    // note: we can't initialise pause_n_async because the simulator doesn't like that
    //       it's assigned with an assign and in an initial, so just make sure
    //       that the resret is longer than pause_n_deasserts_after_ps
    // note: The following works in questasim, but VCS doesn't like it
    //assign #(pause_n_deasserts_after_ps, pause_n_asserts_after_ps) pause_n_async = pcd_pause_n;
    always_comb begin
        if (!pcd_pause_n) begin
            // pcd_pause_n asserted
            pause_n_async <= #pause_n_asserts_after_ps 1'b0;
        end
        else begin
            // pcd_pause_n deasserted
            pause_n_async <= #pause_n_deasserts_after_ps 1'b1;
        end
    end

    // ------------------------------------------------------------------------
    // Variable get / set functions
    // ------------------------------------------------------------------------

    function void set_delays(int new_pause_n_asserts_after_ps,
                             int new_pause_n_deasserts_after_ps);
        pause_n_asserts_after_ps    = new_pause_n_asserts_after_ps;
        pause_n_deasserts_after_ps  = new_pause_n_deasserts_after_ps;
    endfunction

endmodule
