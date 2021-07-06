/***********************************************************************
        File: frame_decode.sv
 Description: Check and remove parity bits
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

module frame_decode
(
    // clk is our 13.56MHz input clock. It is recovered from the carrier wave,
    // and as such stops during pause frames. It must not have any glitches.
    input                   clk,

    // rst is our active low synchronised asynchronous reset signal
    input                   rst_n,

    // from 14443_2a
    rx_interface.in_bit     in_iface,

    // outputs
    rx_interface.out_bit    out_iface,
    output logic            last_bit    // includes parity, but not EOC, used by the FDT
);

    // pass through soc
    // we don't pass eoc straight through, because we want to delay it one tick
    // so it occurs at the same time as error if we are missing the parity bit
    // some for data, we want it to be in sync with data_valid
    assign out_iface.soc = in_iface.soc;

    logic       next_bit_is_parity; // after every 8 bits of data we expect a parity bit
    logic       expected_parity;    // what should the parity bit be
    logic       data_received;      // a 0 bit frame is an error
    logic       error_detected;     // don't issue data after we detect an error
    logic [2:0] bit_count;

    // VCS doesn't generate a valid SAIF file, if I assign to interface members directly
    // in a sequential block.
    logic out_iface_eoc;
    logic out_iface_data_valid;
    logic out_iface_error;
    logic out_iface_data;

    assign out_iface.eoc        = out_iface_eoc;
    assign out_iface.data_valid = out_iface_data_valid;
    assign out_iface.error      = out_iface_error;
    assign out_iface.data       = out_iface_data;

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            out_iface_data_valid    <= 1'b0;
            out_iface_error         <= 1'b0;
            out_iface_eoc           <= 1'b0;
            last_bit                <= 1'b0;
            next_bit_is_parity      <= 1'b0;
        end
        else begin
            // these should only be asserted for one tick
            out_iface_data_valid    <= 1'b0;
            out_iface_error         <= 1'b0;
            out_iface_eoc           <= 1'b0;

            if (in_iface.soc) begin
                // new frame

                // by the time we check bit_count we'll have just received our first bit
                // so initialise it to 1
                bit_count           <= 3'd1;
                expected_parity     <= 1'b1;
                next_bit_is_parity  <= 1'b0;
                error_detected      <= 1'b0;
                data_received       <= 1'b0;
            end

            if (in_iface.eoc) begin
                // EOC
                out_iface_eoc <= 1'b1;

                // we error if we were expecting a parity bit
                // or if we have received no data
                if (!error_detected &&
                    (next_bit_is_parity || !data_received)) begin
                    out_iface_error <= 1'b1;
                    error_detected  <= 1'b1;
                end
            end

            // once we've detected an error, do nothing until the next SOC (other than emit EOC)
            if (!error_detected) begin
                // valid data from the sequence_decode module
                // it's either parity or actual data
                if (in_iface.data_valid) begin
                    data_received   <= 1'b1;
                    last_bit        <= in_iface.data;

                    if (next_bit_is_parity) begin
                        next_bit_is_parity  <= 1'b0;

                        if (in_iface.data != expected_parity) begin
                            // parity error
                            out_iface_error <= 1'b1;
                            error_detected  <= 1'b1;
                        end

                        // reset expected_parity for the next bit
                        expected_parity     <= 1'b1;
                    end
                    else begin
                        bit_count               <= bit_count + 1'd1;

                        // not a parity bit, so pass it through
                        out_iface_data_valid    <= 1'b1;
                        out_iface_data          <= in_iface.data;

                        // odd parity (expecting number of 1s to be odd)
                        expected_parity <= expected_parity ^ in_iface.data;

                        if (bit_count == 0) begin
                            // received 8 bits, next bit is the parity bit
                            next_bit_is_parity  <= 1'b1;
                        end
                    end
                end

                // error from the sequence_decode module
                if (in_iface.error) begin
                    error_detected  <= 1'b1;
                    out_iface_error <= 1'b1;
                end
            end
        end
    end

endmodule
