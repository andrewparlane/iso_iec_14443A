/***********************************************************************
        File: iso14443a_top.sv
 Description: Top Level module for the ISO 14443A IP core
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

// SDC: create_clock - 13.56MHz +/- 7KHz + extra jitter?

module iso14443a_top
#
(
    // Some components need slight tweaks to work for the emulator project
    parameter bit EMULATOR_PROJECT = 0
)
(
    // clk is our 13.56MHz input clock. It is recovered from the carrier wave,
    // and as such stops during pause frames. It must not have any glitches.
    input           clk,

    // rst_n is an asynchronous active low reset.
    // It passes through a reset synchroniser here.
    // rst_n_synchronised should be used everywhere else.
    input           rst_n,

    // pause_n is an asynchronous input from the analogue block.
    // It is essentially the digitized envelope of the carrier wave.
    // When idle pause_n is a 1, when a pause is detected it's a 0.
    // This signal is synchronised in the Rx block
    input           pause_n
);

    logic rst_n_synchronised;

    active_low_reset_synchroniser reset_synchroniser
    (
        .clk        (clk),
        .rst_n_in   (rst_n),
        .rst_n_out  (rst_n_synchronised)
    );


    logic       soc;
    logic       eoc;
    logic [7:0] data;
    logic [2:0] data_bits;
    logic       data_valid;
    logic       sequence_error;
    logic       parity_error;

    rx
    #(
        .EMULATOR_PROJECT   (EMULATOR_PROJECT)
    )
    rx_inst
    (
        .clk                (clk),
        .rst_n              (rst_n_synchronised),
        .pause_n            (pause_n),

        .soc                (soc),
        .eoc                (eoc),
        .data               (data),
        .data_bits          (data_bits),
        .data_valid         (data_valid),
        .sequence_error     (sequence_error),
        .parity_error       (parity_error)
    );

endmodule
