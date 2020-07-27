/***********************************************************************
        File: active_low_reset_synchroniser.sv
 Description: Reset Synchroniser for active low asynchro resets
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

// Reset syncroniser for active low resets
// On rst_n_in asserting, rst_n_out immediately asserts.
// On rst_n_in deasserting, rst_n_out deasserts after the second rising edge of the clock

// There are two FFDs connected in series (2 entry shift register).
// The rst_n_in signal is connected to the asynch RESET input of both FFDs.
// The D input to the first FFD is '1'.
// The Q output of the second FFD is the synchronised reset signal.

// SDC: set_false_path

module active_low_reset_synchroniser
(
    input               clk,
    input               rst_n_in,
    output logic        rst_n_out
);

    logic shift_reg[2];

    assign rst_n_out = shift_reg[1];

    always_ff @(posedge clk, negedge rst_n_in) begin
        if (!rst_n_in) begin
            // rst_in asserted (asynchronous)
            // set both FFDs to 0 immediately (propagate reset assertions immediately)
            shift_reg[0]    <= 1'b0;
            shift_reg[1]    <= 1'b0;
        end
        else begin
            // on the rising edge of the clock (while not in reset)
            // shift '1' through the two FFDs
            shift_reg[0]    <= 1'b1;
            shift_reg[1]    <= shift_reg[0];
        end
    end

endmodule
