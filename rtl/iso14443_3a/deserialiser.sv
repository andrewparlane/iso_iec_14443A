/***********************************************************************
        File: deserialiser.sv
 Description: Convert a series of bits into bytes (rx path)
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

module deserialiser
(
    // clk is our 13.56MHz input clock.
    input                   clk,

    // rst_n is our active low synchronised asynchronous reset signal
    input                   rst_n,

    // input data
    rx_interface.in_bit     in_iface,

    // output data
    rx_interface.out_byte   out_iface
);

    // VCS doesn't generate a valid SAIF file, if I assign to interface members directly
    // in a sequential block.
    logic       out_iface_eoc;
    logic       out_iface_data_valid;
    logic [2:0] out_iface_data_bits;
    logic       out_iface_error;
    logic [7:0] out_iface_data;

    assign out_iface.eoc        = out_iface_eoc;
    assign out_iface.data_valid = out_iface_data_valid;
    assign out_iface.data_bits  = out_iface_data_bits;
    assign out_iface.error      = out_iface_error;
    assign out_iface.data       = out_iface_data;

    assign out_iface.soc        = in_iface.soc;

    logic seen_error;

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            out_iface_data_valid    <= 1'b0;
            out_iface_eoc           <= 1'b0;
            out_iface_error         <= 1'b0;
        end
        else begin
            // these should only be asserted for at most one tick
            out_iface_eoc           <= 1'b0;
            out_iface_data_valid    <= 1'b0;

            // just pass this through (but delayed by a tick, so it stays in sync)
            // and record it so we don't issue future valid data signals
            out_iface_error <= in_iface.error;
            if (in_iface.error) begin
                seen_error      <= 1'b1;
            end

            if (in_iface.soc) begin
                // start a new byte
                out_iface_data_bits <= '0;
                seen_error          <= 1'b0;
            end

            if (in_iface.eoc) begin
                // end of comms
                // send out what we've got if any

                // in_iface.data_valid should never be set at the same time as in_iface.eoc
                // so no need to worry about receiving more data at this point
                if ((out_iface.data_bits != 0) && !seen_error && !in_iface.error) begin
                    out_iface_data_valid <= 1'b1;
                end

                out_iface_eoc <= 1'b1;
            end

            if (in_iface.data_valid && !seen_error) begin
                // we rx LSbit first
                // we could shift into the MSb, but then partial bytes will have issues
                // we could add a "continue_shifting_after_eoc" counter?
                // TODO: work out what's most efficient
                out_iface_data[out_iface.data_bits] <= in_iface.data;

                // note that we've received a bit
                out_iface_data_bits <= out_iface.data_bits + 1'd1;

                // is this a full byte (7 now -> 8 when valid asserts)
                if (out_iface.data_bits == 7) begin
                    out_iface_data_valid <= 1'b1;
                end
            end
        end
    end

endmodule
