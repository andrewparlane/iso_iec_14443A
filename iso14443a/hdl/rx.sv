/***********************************************************************
        File: rx.sv
 Description: Code to receive data from the PCD
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

module rx
#
(
    // Some components need slight tweaks to work for the emulator project
    parameter bit EMULATOR_PROJECT = 0
)
(
    // clk is our 13.56MHz input clock. It is recovered from the carrier wave,
    // and as such stops during pause frames. It must not have any glitches.
    input               clk,

    // rst is our active low synchronised asynchronous reset signal
    input               rst_n,

    // pause_n_synchronised is the synchronised pause_n signal.
    // since the clock stops during pause frames, we can only expect pause_n_synchronised
    // to be asserted (0) for a couple of clock ticks.
    // So we just look for rising edges (end of pause)
    input               pause_n_synchronised,

    // Outputs
    output logic        soc,
    output logic        eoc,
    output logic [7:0]  data,
    output logic [2:0]  data_bits,
    output logic        data_valid,
    output logic        sequence_error,
    output logic        parity_error,
    output logic        last_bit            // includes parity, but not EOC, used by the FDT
);

    import ISO14443A_pkg::*;

    // ========================================================================
    // The sequence_decode component
    // ========================================================================

    // This turns the pause_n_synchronised signal into PCDBitSequences
    PCDBitSequence  sd_seq;
    logic           sd_valid;
    logic           sd_idle;

    sequence_decode
    #(
        .EMULATOR_PROJECT   (EMULATOR_PROJECT)
    )
    sd_inst
    (
        .clk                    (clk),
        .rst_n                  (rst_n),

        .pause_n_synchronised   (pause_n_synchronised),

        // outputs
        .seq                    (sd_seq),
        .seq_valid              (sd_valid),
        .idle                   (sd_idle)
    );

    // ========================================================================
    // The frame_decode component
    // ========================================================================

    // This turns the PCDBitSequences into:
    //  SOC (start of comms)
    //  EOC (end of comms)
    //  data
    //  errors
    // It checks and then drops the parity bit (if any)

    frame_decode fd_inst
    (
        .clk                (clk),

        .rst_n              (rst_n),

        .sd_seq             (sd_seq),
        .sd_seq_valid       (sd_valid),

        // outputs
        .soc                (soc),
        .eoc                (eoc),
        .data               (data),
        .data_bits          (data_bits),
        .data_valid         (data_valid),
        .sequence_error     (sequence_error),
        .parity_error       (parity_error),
        .last_bit           (last_bit)
    );

endmodule
