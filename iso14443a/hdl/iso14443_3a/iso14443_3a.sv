/***********************************************************************
        File: iso14443_3a.sv
 Description: ISO/IEC 14443-3A code
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

module iso14443_3a
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
    parameter int FDT_TIMING_ADJUST
)
(
    // clk is our 13.56MHz input clock. It is recovered from the carrier wave,
    // and as such stops during pause frames. It must not have any glitches.
    input                       clk,

    // rst is our active low synchronised asynchronous reset signal
    input                       rst_n,

    // The variable part of the UID
    // should come from flash or dip switches / wire bonding / hardcoded
    // I assume this is constant in my code. So I'd recommend only changing it
    // while this IP core is in reset. That may not be strictly necesarry, but
    // further investigation would be necesarry to be sure.
    input [UID_INPUT_BITS-1:0]  uid_variable,

    // pause_n_synchronised is the synchronised pause_n signal.
    // since the clock stops during pause frames, we can only expect pause_n_synchronised
    // to be asserted (0) for a couple of clock ticks.
    // So we just look for rising edges (end of pause)
    input                       pause_n_synchronised,

    // Rx interface from 14443_2a
    rx_interface.in_bit         in_rx_iface,

    // Rx interface to 14443_4
    rx_interface.out_byte       out_rx_iface,
    output logic                rx_crc_ok,

    // Tx interface to 14443_2a
    tx_interface.out_bit        out_tx_iface
);

    rx_interface #(.BY_BYTE(0)) rx_iface_bits  (.*);
    rx_interface #(.BY_BYTE(1)) rx_iface_bytes (.*);
    tx_interface #(.BY_BYTE(1)) tx_iface (.*);

    logic tx_append_crc;
    framing
    #(
        .FDT_TIMING_ADJUST      (FDT_TIMING_ADJUST)
    )
    framing_inst
    (
        .clk                    (clk),
        .rst_n                  (rst_n),

        .pause_n_synchronised   (pause_n_synchronised),

        // Rx interface from 14443_2a
        .in_rx_iface            (in_rx_iface),

        // Rx interfaces to initialisation/14443_4
        .out_rx_iface_bytes     (rx_iface_bytes),
        .out_rx_iface_bits      (rx_iface_bits),
        .rx_crc_ok              (rx_crc_ok),

        // Tx interface from initialisation/14443_4
        .in_tx_iface            (tx_iface),
        .tx_append_crc          (tx_append_crc),

        // Tx interface to 14443_2a
        .out_tx_iface           (out_tx_iface)
    );

    logic iso14443_4_deselect;
    assign iso14443_4_deselect = 1'b0;

    initialisation
    #(
        .UID_SIZE               (UID_SIZE),
        .UID_INPUT_BITS         (UID_INPUT_BITS),
        .UID_FIXED              (UID_FIXED)
    )
    initialisation_inst
    (
        .clk                    (clk),
        .rst_n                  (rst_n),

        .uid_variable           (uid_variable),

        .rx_iface               (rx_iface_bytes),
        .rx_iface_bits          (rx_iface_bits),
        .rx_crc_ok              (rx_crc_ok),

        .iso14443_4_deselect    (iso14443_4_deselect),

        .tx_iface               (tx_iface),
        .tx_append_crc          (tx_append_crc)
    );

    // TODO: routing
    assign out_rx_iface.soc         = 1'b0;
    assign out_rx_iface.eoc         = 1'b0;
    assign out_rx_iface.error       = 1'b0;
    assign out_rx_iface.data_valid  = 1'b0;

endmodule
