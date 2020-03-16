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

`timescale 1ps/1ps

// SDC: create_clock - 13.56MHz +/- 7KHz + extra jitter?

module iso14443a_top
#(
    // Are we using single, double or triple UIDs
    parameter ISO14443A_pkg::UIDSize                                            UID_SIZE,

    // How many UID bits are variable (via the uid input port)?
    // must be > 0 and <= the total number of bits in the UID
    // If you want a fixed UID then you can just set this to 1 and hardcode
    // uid[0] to whatever you want.
    parameter int                                                               UID_INPUT_BITS,

    // The fixed bits of the UID
    // the final UID is {UID_FIXED, uid_variable}
    parameter logic [ISO14443A_pkg::get_uid_bits(UID_SIZE)-UID_INPUT_BITS-1:0]  UID_FIXED,

    // see fdt.sv
    // TODO: should we add in the delays in frame_encode and tx automatically?
    //       or expect them to be specified here?
    // TODO: Maybe add a generate here saying FDT_TIMING_ADJUST MUST BE SET
    //       default to -1 and if it's not >= 0 then error?
    parameter int FDT_TIMING_ADJUST
)
(
    // clk is our 13.56MHz input clock. It is recovered from the carrier wave,
    // and as such stops during pause frames. It must not have any glitches.
    input                       clk,

    // rst_n is an asynchronous active low reset.
    // It passes through a reset synchroniser here.
    // rst_n_synchronised should be used everywhere else.
    input                       rst_n,

    // The variable part of the UID
    // should come from flash or dip switches / wire bonding / hardcoded
    // I assume this is constant in my code. So I'd recommend only changing it
    // while this IP core is in reset. That may not be strictly necesarry, but
    // further investigation would be necesarry to be sure.
    input [UID_INPUT_BITS-1:0]  uid_variable,

    // pause_n is an asynchronous input from the analogue block.
    // It is essentially the digitized envelope of the carrier wave.
    // When idle pause_n is a 1, when a pause is detected it's a 0.
    // This signal is synchronised before use
    input                       pause_n,

    // tx_out is the manchester encoded data AND'ed with the subcarrier
    // this should be connected to the load modulator
    output logic                tx_out
);

    logic rst_n_synchronised;
    active_low_reset_synchroniser reset_synchroniser
    (
        .clk        (clk),
        .rst_n_in   (rst_n),
        .rst_n_out  (rst_n_synchronised)
    );

    // The pause_n signal is asynchronous it can assert / deassert at any point
    // during the clock cycle. Additionally the clock will not be running during
    // a pause frame, and so pause_n <may> assert and deassert between rising
    // clock edges.

    // To handle this we pass it through an active low reset synchroniser.
    // When pause_n goes low, both FFDs in the synchroniser are reset to 0.
    // Once pause_n goes high, a 1 is shifted through both FFDs. So two clock ticks
    // later we detect the rising edge, indicating the end of pause frame.

    logic pause_n_synchronised;
    active_low_reset_synchroniser pause_n_synchroniser
    (
        .clk        (clk),
        .rst_n_in   (pause_n),
        .rst_n_out  (pause_n_synchronised)
    );

    rx_interface
    #(
        .BY_BYTE    (0)
    )
    part2_to_part3_rx_iface
    (
        .clk        (clk),
        .rst_n      (rst_n)
    );

    rx_interface
    #(
        .BY_BYTE    (1)
    )
    part3_to_part4_rx_iface
    (
        .clk        (clk),
        .rst_n      (rst_n)
    );

    tx_interface
    #(
        .BY_BYTE    (0)
    )
    part3_to_part2_tx_iface
    (
        .clk        (clk),
        .rst_n      (rst_n)
    );

    iso14443_2a part2
    (
        .clk                    (clk),
        .rst_n                  (rst_n),

        .pause_n_synchronised   (pause_n_synchronised),

        .rx_iface               (part2_to_part3_rx_iface),
        .tx_iface               (part3_to_part2_tx_iface),

        .tx_out                 (tx_out)
    );

    iso14443_3a
    #(
        .UID_SIZE               (UID_SIZE),
        .UID_INPUT_BITS         (UID_INPUT_BITS),
        .UID_FIXED              (UID_FIXED),
        .FDT_TIMING_ADJUST      (FDT_TIMING_ADJUST+2) // TODO: check this +2 is correct
    )
    part3
    (
        .clk                    (clk),
        .rst_n                  (rst_n),

        .uid_variable           (uid_variable),

        .pause_n_synchronised   (pause_n_synchronised),

        .in_rx_iface            (part2_to_part3_rx_iface),
        .out_rx_iface           (part3_to_part4_rx_iface),

        .out_tx_iface           (part3_to_part2_tx_iface)
    );

endmodule
