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
    // These variables must be set to correctly emulate the analogue block.
    // Preferably the final verification will be run numerous times with these variables
    // randomised within the expected range due to PVT.

    // ------------------------------------------------------------------------
    // Variables
    // ------------------------------------------------------------------------

    // looking at figure 5.11 in Fabricio's thesis we see that pause_n_async asserts
    // ~1 us after the PCD starts the pause, and deasserts it ~150 ns after
    // the PCD ends the pause
    int pause_n_asserts_after_ps    = 1 * 1000 * 1000;  // 1us
    int pause_n_deasserts_after_ps  =      150 * 1000;  // 150 ns

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
