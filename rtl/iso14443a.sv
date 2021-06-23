/***********************************************************************
        File: iso14443a.sv
 Description: Top Level module for the ISO 14443A IP core
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

module iso14443a
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

    // see fdt.sv for more details.
    // We have already accounted for the delay in the internal Tx path. We pass the
    // FDT_TIMING_ADJUST parametr with a +3 below and a +1 in the framing module.
    // All remaining delays can not be calculated here, as they depend on the AFE.
    //
    // This parameter should be set as follows:
    //      PCD_PAUSE_N_TO_SYNCHRONISED_PS - This should be the time in ps between the start of
    //                                       the rising edge of the analogue RF signal (see small
    //                                       circles in Figure 3 of ISO/IEC 14443-2:2016, I think
    //                                       the one labled as 5, but the docs aren't clear),
    //                                       and the rising edge of the pause_n_synchronised signal.
    //                                       We can't account for the delay in the synchroniser
    //                                       automatically, because it depends on when the end of pause
    //                                       is detected and when the clock starts up again.
    //
    //      LM_OUT_TO_MODULATION_EDGE_PS   - This should be the time in ps between the rising edge of
    //                                       the lm_out signal and the load modulator activating.
    //                                       Which includes any output buffering, and propagation delays
    //                                       in the analogue front end.
    //
    // Both of these should be set to the MINIMUM possible values, since the spec states that we can
    // be a up to 0.4us late but must not be early.
    //
    // Finally FDT_TIMING_ADJUST should be set to the sum of these divided by the MAXIMUM possible
    // clock period and rounded DOWN. (MAX clock period and rounded DOWN, due to the same reason as
    // above).
    //
    // FDT_TIMING_ADJUST = $rtoi((PCD_PAUSE_N_TO_SYNCHRONISED_PS + LM_OUT_TO_MODULATION_EDGE_PS)
    //                              / MAX_CLOCK_PERIOD_PS);
    // where MAX_CLOCK_PERIOD_PS is 1/(13.56MHz - 7KHz) = 73,784.4 ps
    //
    // Making it signed, and the default -1, so I can generate an error if it's not correctly set
    parameter int signed FDT_TIMING_ADJUST = -1
)
(
    // clk is our 13.56MHz input clock. It is recovered from the carrier wave,
    // and as such stops during pause frames. It must not have any glitches.
    input                       clk,

    // rst_n is an asynchronous active low reset, that has passed through a reset synchroniser
    // so that the rising edge is synchronous to the clk.
    input                       rst_n,

    // The variable part of the UID
    // should come from flash or dip switches / wire bonding / hardcoded
    // I assume this is constant in my code. So I'd recommend only changing it
    // while this IP core is in reset. That may not be strictly necesarry, but
    // further investigation would be necesarry to be sure.
    input [UID_INPUT_BITS-1:0]  uid_variable,

    // Every reply from the PICC that includes a CID field also includes a power indicator
    // field to tell the PCD if it's receiving enough power or not. The PCD can then adjust
    // it's power output as needed.
    //
    // The analogue block should pass the correct value in. It can change over time.
    // and must be synchronised before being passed in.
    //
    // ISO/IEC 14443-4:2016 section 7.4 states:
    //      2'b00: PICC does not support the power level indiction
    //      2'b01: Insufficient power for full functionality
    //      2'b10: Sufficient power for full functionality
    //      2'b11: More than sufficient power for full functionality
    input [1:0]                 power,

    // pause_n_synchronised is the output of the pause_n_latch_and_synchroniser module, we take
    // this as an input here instead of latching and synchronising it in this module since other
    // parts of the design may also want access to the latched and synchronised signal.
    input                       pause_n_synchronised,

    // lm_out is the manchester encoded data AND'ed with the subcarrier
    // this should be connected to the load modulator
    output logic                lm_out,

    // The interface with the application.
    // The INF field of received STD I-Blocks is forwarded to the app on the app_rx_iface.
    // The app may respond with the INF field using the app_tx_iface.
    // When app_resend_last asserts, the app should send the same reply as it did to the last message.
    rx_interface.out_byte       app_rx_iface,
    tx_interface.in_byte        app_tx_iface,
    output logic                app_resend_last
);

    // The version of this IP core
    // can be accessed via heirarcical naming
    localparam int ISO_IEC_14443A_VERSION = 1;

    // check the FDT_TIMING_ADJUST signal has been set
    generate
        if (FDT_TIMING_ADJUST < 0) begin
            synth_time_error fdt_timing_adjust_must_be_set(.*);
        end
    endgenerate

    // ========================================================================
    // ISO/IEC 14443-2A
    // ========================================================================

    rx_interface #(.BY_BYTE(0)) part2_to_part3_rx_iface (.*);
    tx_interface #(.BY_BYTE(0)) part3_to_part2_tx_iface (.*);

    iso14443_2a part2
    (
        .clk                    (clk),
        .rst_n                  (rst_n),

        .pause_n_synchronised   (pause_n_synchronised),

        .rx_iface               (part2_to_part3_rx_iface),
        .tx_iface               (part3_to_part2_tx_iface),

        .lm_out                 (lm_out)
    );

    // ========================================================================
    // ISO/IEC 14443-3A
    // ========================================================================

    rx_interface #(.BY_BYTE(1)) part3_to_part4_rx_iface (.*);
    tx_interface #(.BY_BYTE(1)) part4_to_part3_tx_iface (.*);

    logic part4_rx_crc_ok;
    logic part4_deselect;
    logic part4_rats;
    logic part4_tag_active;
    logic part4_tx_append_crc;

    iso14443_3a
    #(
        .UID_SIZE               (UID_SIZE),
        .UID_INPUT_BITS         (UID_INPUT_BITS),
        .UID_FIXED              (UID_FIXED),
        // We use +3 here because of delays in the Tx path in the iso14443_2a module
        // see the comments at the start of fdt.sv
        .FDT_TIMING_ADJUST      (FDT_TIMING_ADJUST+3)
    )
    part3
    (
        .clk                    (clk),
        .rst_n                  (rst_n),

        .uid_variable           (uid_variable),

        .pause_n_synchronised   (pause_n_synchronised),

        .rx_iface_from_14443_2a (part2_to_part3_rx_iface),
        .tx_iface_to_14443_2a   (part3_to_part2_tx_iface),

        .rx_iface_to_14443_4a   (part3_to_part4_rx_iface),
        .rx_crc_ok              (part4_rx_crc_ok),
        .tx_iface_from_14443_4a (part4_to_part3_tx_iface),
        .tx_append_crc_14443_4a (part4_tx_append_crc),

        .iso14443_4a_deselect   (part4_deselect),
        .iso14443_4a_rats       (part4_rats),
        .iso14443_4a_tag_active (part4_tag_active)
    );

    // ========================================================================
    // ISO/IEC 14443-4A
    // ========================================================================

    iso14443_4a part4
    (
        .clk                    (clk),
        .rst_n                  (rst_n),

        .power                  (power),

        .rx_iface               (part3_to_part4_rx_iface),
        .rx_crc_ok              (part4_rx_crc_ok),
        .tx_iface               (part4_to_part3_tx_iface),
        .tx_append_crc          (part4_tx_append_crc),

        .tag_active             (part4_tag_active),

        .rx_rats                (part4_rats),
        .rx_deselect            (part4_deselect),

        .app_rx_iface           (app_rx_iface),
        .app_tx_iface           (app_tx_iface),
        .app_resend_last        (app_resend_last)
    );

endmodule
