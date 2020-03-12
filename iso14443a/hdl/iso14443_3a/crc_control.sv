/***********************************************************************
        File: crc_control.sv
 Description: Take the CRC_A of the Rx or the Tx bit stream?
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

module crc_control
(
    // clk is our 13.56MHz input clock. It is recovered from the carrier wave,
    // and as such stops during pause frames. It must not have any glitches.
    input                   clk,

    // rst is our active low synchronised asynchronous reset signal
    input                   rst_n,

    // Rx interface
    rx_interface.in_bit     rx_iface,
    output logic            rx_crc_ok,

    // Tx interface
    tx_interface.in_bit     tx_iface,
    input                   tx_append_crc,  // we only calculate the Tx CRC if we will use it
    input                   fdt_trigger,    // we only start the CRC calculation on the fdt_trigger
    output logic [15:0]     crc
);

    logic crc_start;
    logic crc_data;
    logic crc_sample;
    crc_a crc_a_inst
    (
        .clk                (clk),
        .rst_n              (rst_n),

        .start              (crc_start),
        .data               (crc_data),
        .sample             (crc_sample),

        .crc                (crc)
    );

    // The Rx CRC is OK if the CRC of all the bytes (including the CRC) is 0
    assign rx_crc_ok = (crc == 0);

    enum
    {
        CRC_Rx,
        CRC_Tx
    } crc_type;

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            crc_type    <= CRC_Rx;
            crc_start   <= 1'b0;
            crc_sample  <= 1'b0;
        end
        else begin
            // these should only ever assert for one tick at a time
            crc_start   <= 1'b0;
            crc_sample  <= 1'b0;

            // Theoretically we can't Tx at the same time as Rx. The FDT ensures that
            // we can't start Tx before the end of Rx. The only other way we could have
            // Rx and Tx at the same time, is if we were transmitting and the PCD starting
            // transmitting before we finished. Which would be a bug in the PCD and in violation
            // of the standard. So we assume that can't happen (and if it does we have bigger
            // problems). Therefore we switch to Rx mode as soon as the rx_iface_bits.soc asserts
            // and switch to Tx as soon as the FDT trigger fires and tx_iface_bits.data_valid
            // is asserted.

            // which mode are we in? and clear the current state when we switch mode
            if (rx_iface.soc) begin
                crc_type    <= CRC_Rx;
                crc_start   <= 1'b1;
            end

            if (tx_iface.data_valid && fdt_trigger && tx_append_crc) begin
                crc_type    <= CRC_Tx;
                crc_start   <= 1'b1;
            end

            // when and what to sample?
            if (crc_type == CRC_Rx) begin
                if (rx_iface.data_valid) begin
                    crc_data    <= rx_iface.data;
                    crc_sample  <= 1'b1;
                end
            end
            else begin
                if (tx_iface.req) begin
                    crc_data    <= tx_iface.data;
                    crc_sample  <= 1'b1;
                end
            end
        end
    end

endmodule
