/***********************************************************************
        File: framing.sv
 Description: Code to do the Rx and Tx parts of the ISO/IEC 14443-3A
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

module framing
#(
    // see fdt.sv
    // we have already accounted for the time it takes between fdt_trigger firing
    // and out_iface.data_valid asserting in the parameter passed to the fdt module
    parameter int FDT_TIMING_ADJUST
)
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

    // Rx interface from 14443_2a
    rx_interface.in_bit     in_rx_iface,

    // Rx interfaces to initialisation/14443_4
    rx_interface.out_byte   out_rx_iface_bytes,
    rx_interface.out_bit    out_rx_iface_bits,
    output logic            rx_crc_ok,

    // Tx interface from initialisation/14443_4
    tx_interface.in_byte    in_tx_iface,
    input logic             tx_append_crc,

    // Tx interface to 14443_2a
    tx_interface.out_bit    out_tx_iface
);

    // ========================================================================
    // Rx
    // ========================================================================
    // The Rx data comes from the 14443-2A block with in_rx_iface as bits
    // The frame_decode module checks and removes the parity bits
    // we record the last_rx bit received (including parity+crc, but not EOC)
    // for use with the FDT.
    // The output of frame_decode is rx_iface_bits which goes to the deserialiser
    // to be turned into a byte stream. It also is passed to the CRC_A module
    // to check the CRC.
    // Both the bit streams and byte streams are outputted from this module.
    // The byte stream is routed to both the initialisation and the iso14443_4 modules
    // The bit stream goes to just the initialisation module, and is used for
    // AC UID checking.

    rx_interface #(.BY_BYTE(0)) rx_iface_bits  (.*);
    logic last_rx_bit;
    frame_decode fd_inst
    (
        .clk        (clk),
        .rst_n      (rst_n),

        .in_iface   (in_rx_iface),

        .out_iface  (rx_iface_bits),
        .last_bit   (last_rx_bit)
    );

    deserialiser ds_inst
    (
        .clk        (clk),
        .rst_n      (rst_n),

        .in_iface   (rx_iface_bits),
        .out_iface  (out_rx_iface_bytes)
    );

    // rx_iface_bits also gets connected to out_rx_iface_bits
    // not sure if there's an easier way to do this?
    assign out_rx_iface_bits.soc        = rx_iface_bits.soc;
    assign out_rx_iface_bits.eoc        = rx_iface_bits.eoc;
    assign out_rx_iface_bits.data       = rx_iface_bits.data;
    assign out_rx_iface_bits.data_valid = rx_iface_bits.data_valid;
    assign out_rx_iface_bits.error      = rx_iface_bits.error;

    // ========================================================================
    // FDT
    // ========================================================================
    // The frame delay timer is used to trigger the start of Tx, so that it occurs
    // at the exact correct time. This is required by ISO/IEC 14443-3:2016 section 6.2.1.1.

    logic fdt_trigger;
    fdt
    #(
        // we use +1 because it takes the frame_encode module one tick to see the
        // FDT trigger before it asserts out_iface.data_valid
        .TIMING_ADJUST          (FDT_TIMING_ADJUST + 1)
    )
    fdt_inst
    (
        .clk                    (clk),
        .rst_n                  (rst_n),
        .pause_n_synchronised   (pause_n_synchronised),
        .last_rx_bit            (last_rx_bit),
        .trigger                (fdt_trigger)
    );

    // ========================================================================
    // Tx
    // ========================================================================
    // The Tx data comes in from the initialisation/14443_4 modules with in_tx_iface
    // as a byte stream. First it gets converted into a bit stream with the serialiser module.
    // The bit stream is passed to the CRC_A module to calculate the CRC, and then to the
    // frame_encode module, which adds the parity bits. The frame_encode module won't
    // start sending until the frame delay timer fires.

    tx_interface #(.BY_BYTE(0)) tx_iface_bits  (.*);
    serialiser s_inst
    (
        .clk                (clk),
        .rst_n              (rst_n),

        .in_iface           (in_tx_iface),
        .out_iface          (tx_iface_bits)
    );

    // TODO: append crc to tx bit stream rather than passing it in to frame_encode separately?

    logic [15:0] crc;
    frame_encode fe_inst
    (
        .clk                (clk),
        .rst_n              (rst_n),

        .fdt_trigger        (fdt_trigger),

        .in_iface           (tx_iface_bits),
        .append_crc         (tx_append_crc),
        .crc                (crc),

        .out_iface          (out_tx_iface)
    );

    // ========================================================================
    // CRC
    // ========================================================================
    // We use one CRC module to check the Rx CRC and to calculate the CRC for Tx

    crc_control crc_inst
    (
        .clk                (clk),
        .rst_n              (rst_n),

        .rx_iface           (rx_iface_bits),
        .rx_crc_ok          (rx_crc_ok),

        .tx_iface           (tx_iface_bits),
        .tx_append_crc      (tx_append_crc),
        .fdt_trigger        (fdt_trigger),
        .crc                (crc)
    );

endmodule
