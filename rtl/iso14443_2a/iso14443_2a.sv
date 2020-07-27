/***********************************************************************
        File: iso14443_2a.sv
 Description: ISO/IEC 14443-2A code
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

// This module implements the digital part of the comms specified in ISO/IEC 14443-2A.
// It consists of the sequence_decode module and the tx module.
// We only support the slowest transfer rate (fc/128)

module iso14443_2a
(
    // clk is our 13.56MHz input clock. It is recovered from the carrier wave,
    // and as such stops during pause frames. It must not have any glitches.
    input                   clk,

    // rst is our active low synchronised asynchronous reset signal
    input                   rst_n,

    // pause_n_synchronised is the synchronised pause_n signal.
    // since the clock stops during pause frames, we can only expect pause_n_synchronised
    // to be asserted (0) for a couple of clock ticks.
    // So we just look for rising edges (end of pause)
    input                   pause_n_synchronised,

    // to 14443_3a (BY_BYTE must be 0)
    rx_interface.out_bit    rx_iface,
    tx_interface.in_bit     tx_iface,

    // lm_out is the manchester encoded data AND'ed with the subcarrier
    // which is sent to the load modulator
    output logic            lm_out
);

    sequence_decode sd_inst
    (
        .clk                    (clk),
        .rst_n                  (rst_n),

        .pause_n_synchronised   (pause_n_synchronised),

        .out_iface              (rx_iface)
    );

    tx tx_inst
    (
        .clk                    (clk),
        .rst_n                  (rst_n),

        .in_iface               (tx_iface),

        .lm_out                 (lm_out)
    );

endmodule
