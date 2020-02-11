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
    input [7:0]         data,
    input               data_valid,     // sample data?

    // For Rx:
    //      Pass all data in including the received CRC. The received CRC is valid,
    //      if this output is 0.
    // For Tx:
    //      Pass in data to send. The resulting CRC should be appended to the data
    //      transmitted, LSByte first
    output logic [15:0] crc
);

    // See ISO/IEC 14443-3:2016 section 6.2.4 and Annex B
    // and software/msp430g2/common/iso14443.c:computeCrc()
    // We could implement this as a LFSR which could use less area but the frame_decoder
    // provides bytes not bits. I could modify it to provide bits received
    // (discounting parity and SOC / EOC) as well but I'm not sure if it'd save much / anything
    // TODO: Look into doing this and see what the difference in area is.

    localparam logic [15:0] INIT = 16'h6363;

    // I can simplify this since A ^ 0 === A
    // but I'm relying on the synopsys tools being clever enough to do that for me
    // TODO: Look at the resulting circuit
    logic [15:0] tmp1;
    logic [15:0] tmp2;
    logic [15:0] tmp3;

    assign tmp1 = {8'd0, data} ^ crc[7:0];
    assign tmp2 = tmp1 ^ {8'd0, tmp1[3:0], 4'd0};
    assign tmp3 = {8'd0, crc[15:8]} ^ {tmp2[7:0], 8'd0} ^ {tmp2[12:0], 3'd0} ^ {4'd0, tmp2[15:4]};

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
        end
        else begin
            if (start) begin
                crc <= INIT;
            end
            else if (data_valid) begin
                crc <= tmp3;
            end
        end
    end

endmodule
