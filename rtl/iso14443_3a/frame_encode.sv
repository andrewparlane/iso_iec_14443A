/***********************************************************************
        File: frame_encode.sv
 Description: Add parity and CRC to the Tx data. Start sending on fdt trigger
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

// Parity bits are added after bits_in_first_byte and then after every 8 bits.
// We use bits_in_first_byte so that we can send the parity bit at the correct time in AC replies.
// After in_iface.data_valid deasserts if the append_crc signal is asserted, we start sending the CRC.

// This module should be connected to the iso14443-2A Tx module

module frame_encode
(
    // clk is our 13.56MHz input clock.
    input                   clk,

    // rst is our active low synchronised asynchronous reset signal
    input                   rst_n,

    // input from the frame delay timer
    // this triggers the send (if in_iface.data_valid is set)
    input                   fdt_trigger,

    // Input data
    tx_interface.in_bit     in_iface,

    input                   append_crc,
    input           [15:0]  crc,

    // Output data
    tx_interface.out_bit    out_iface
);

    enum
    {
        State_IDLE,
        State_DATA,
        State_PARITY,
        State_CRC,
        State_CRC_PARITY,
        State_END
    } state;

    // bits remaining before sending parity bit
    logic [2:0]     bits_remaining;
    logic           parity;

    logic [15:0]    cached_crc;
    logic           crc_byte;

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            state                   <= State_IDLE;
            in_iface.req            <= 1'b0;
            out_iface.data_valid    <= 1'b0;
        end
        else begin
            // req should only ever be asserted one tick at a time
            in_iface.req    <= 1'b0;

            case (state)
                State_IDLE: begin
                    // we're idle
                    // wait for fdt_trigger
                    if (fdt_trigger) begin
                        // start if data valid
                        if (in_iface.data_valid) begin
                            // start sending data
                            out_iface.data              <= in_iface.data;
                            out_iface.data_valid        <= 1'b1;
                            out_iface.last_bit_in_byte  <= 1'b0;
                            parity                      <= !in_iface.data;

                            if (in_iface.last_bit_in_byte) begin
                                // send parity bit next
                                state   <= State_PARITY;
                            end
                            else begin
                                state   <= State_DATA;
                            end

                            // and request the next bit
                            in_iface.req    <= 1'b1;
                        end
                    end
                end

                State_DATA: begin
                    // when the REQ comes in from the 14443-2 Tx module then send out the next data bit
                    if (out_iface.req) begin
                        // note: We ignore in_iface.data_valid here as PICC -> PCD comms should always
                        // end with a parity bit. The sender should take care to always send the correct
                        // number of bits

                        // send the next bit and update the parity bit
                        out_iface.data              <= in_iface.data;
                        out_iface.last_bit_in_byte  <= 1'b0;
                        parity                      <= parity ^ in_iface.data;

                        if (in_iface.last_bit_in_byte) begin
                            // sending the last bit of this byte
                            // next bit is the parity bit
                            state   <= State_PARITY;
                        end

                        // request the next bit
                        in_iface.req    <= 1'b1;
                    end
                end

                State_PARITY: begin
                    // wait for the bit encoder to request more data
                    if (out_iface.req) begin
                        // send the parity bit
                        out_iface.data              <= parity;
                        out_iface.last_bit_in_byte  <= 1'b1;

                        // anything more to send?
                        if (in_iface.data_valid) begin
                            // yep
                            state           <= State_DATA;
                            parity          <= 1'b1;
                        end
                        else if (append_crc) begin
                            // no more data to send, but we have the CRC to send
                            cached_crc      <= crc;
                            bits_remaining  <= 3'd0;
                            crc_byte        <= 1'd0;    // CRC gets sent out LSByte first
                            parity          <= 1'b1;
                            state           <= State_CRC;
                        end
                        else begin
                            // nothing more to send
                            state           <= State_END;
                        end
                    end
                end

                State_CRC: begin
                    // when the REQ comes in from the 14443-2 Tx module then send out the next crc bit
                    if (out_iface.req) begin
                        // send the next bit and update the parity bit and shift the crc right by one
                        out_iface.data              <= cached_crc[0];
                        out_iface.last_bit_in_byte  <= 1'b0;
                        cached_crc[14:0]            <= cached_crc[15:1];
                        parity                      <= parity ^ cached_crc[0];

                        if (bits_remaining == 1) begin
                            // sending the last bit of this byte
                            // next bit is the parity bit
                            state   <= State_CRC_PARITY;
                        end

                        bits_remaining  <= bits_remaining - 1'd1;
                    end
                end

                State_CRC_PARITY: begin
                    // wait for the bit encoder to request more data
                    if (out_iface.req) begin
                        // send the parity bit
                        out_iface.data              <= parity;
                        out_iface.last_bit_in_byte  <= 1'b1;

                        // anything more to send?
                        if (crc_byte == 0) begin
                            // send the nex crc byte
                            crc_byte        <= 1'b1;
                            parity          <= 1'b1;
                            bits_remaining  <= 3'd0;
                            state           <= State_CRC;
                        end
                        else begin
                            // nothing more to send
                            state           <= State_END;
                        end
                    end
                end

                State_END: begin
                    // wait for the bit encoder to request more data
                    if (out_iface.req) begin
                        // no more data to send
                        out_iface.data_valid    <= 1'b0;
                        state                   <= State_IDLE;
                    end
                end

                default: begin
                    state <= State_IDLE;
                end
            endcase
        end
    end

endmodule
