/***********************************************************************
        File: crc_a.sv
 Description: Generates the CRC_A defined in ISO 14443-3 Annex B
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

module crc_a
(
    // clk is our 13.56MHz input clock.
    input               clk,

    // rst_n is our active low synchronised asynchronous reset signal
    input               rst_n,

    input               start,          // starts calculating a new CRC
    input               data,
    input               sample,         // sample data?

    // For Rx:
    //      Pass all data in including the received CRC. The received CRC is valid,
    //      if this output is 0.
    // For Tx:
    //      Pass in data to send. The resulting CRC should be appended to the data
    //      transmitted, LSByte first
    output logic [15:0] crc
);

    // See ISO/IEC 14443-3:2016 section 6.2.4 and Annex B
    // polynomial of x^16 + x^12 + x^5 + 1

    // note here we use 0:15 to match the definition given in Annex B
    localparam logic [0:15] INIT = 16'h6363;

    logic [0:15] lfsr;

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            lfsr <= INIT;
        end
        else begin
            if (start) begin
                lfsr <= INIT;
            end
            else if (sample) begin
                // shift everything right by one
                for (int i = 1; i <= 15; i++) begin
                    lfsr[i] <= lfsr[i-1];
                end

                // except for bits 12, 5, 0
                lfsr[12]    <= lfsr[15] ^ lfsr[11] ^ data;
                lfsr[5]     <= lfsr[15] ^ lfsr[4] ^ data;
                lfsr[0]     <= lfsr[15] ^ data;
            end
        end
    end

    assign crc = lfsr;

endmodule
