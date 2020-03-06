/***********************************************************************
        File: bit_encoder.sv
 Description: Manchester encodes bits for transmission
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

module bit_encoder
(
    // clk is our 13.56MHz input clock.
    input               clk,

    // rst_n is our active low synchronised asynchronous reset signal
    input               rst_n,

    // are we generating output?
    input               en,

    // data to encode
    // we ignore data_valid here and just assume it's valid if we are enabled
    tx_interface.in_bit in_iface,

    // output data
    output logic        encoded_data,

    // end of bit time
    output logic        last_tick
);
    // ISO/IEC 14443-2:2016 section 8.2.1 The bit time is 128 ticks.
    // need to count 0 - 127 -> 7 bits
    logic [6:0] count;

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            count   <= '0;
        end
        else begin
            if (en) begin
                // always increment when enabled
                count <= count + 1'd1;

                if (count == 0) begin
                    // ISO/IEC 14443-2:2016 section 8.2.5.1
                    //  0: low for the first half, high for the second
                    //  1: high for the first half, low for the second
                    // first tick, set encoded_data to the first half of the bit period
                    encoded_data <= in_iface.data;
                end
                else if (count == 64) begin
                    // half way through the bit period, so invert encoded_data
                    encoded_data <= !encoded_data;
                end
            end
            else begin
                count <= '0;
            end
        end
    end

    // output if we are on the last tick of the bit period
    assign last_tick = (count == 127);

    // request more data when we are halfway through the bit period
    // we could do this at anytime but this should reuse the == 64 comparitor
    // that we already have
    assign in_iface.req = (count == 64);

endmodule
