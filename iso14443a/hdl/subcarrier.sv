/***********************************************************************
        File: subcarrier.sv
 Description: Generates the subcarrier for PICC -> PCD comms
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

module subcarrier
(
    // clk is our 13.56MHz input clock.
    input               clk,

    // rst_n is our active low synchronised asynchronous reset signal
    input               rst_n,

    // Enable the subcarrier generator?
    // According to ISO/IEC 14443-2:2016 section 8.2.3
    // The subcarrier should only be generated when data is to be transmitted
    // plus this saves power
    input               en,

    // the subcarrier output
    // Note: this initially asserts 1 tick after enable asserts
    //       make sure that the manchester encoding module also starts
    //       generating the bit one tick after en asserts
    output logic        subcarrier
);
    // According to ISO/IEC 14443-2:2016 section 8.2.3.1
    // the subcarrier has frequency of the clk / 16
    // so we toggle the subcarrier output every 8 ticks

    logic [2:0] count;

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            count       <= '0;
            subcarrier  <= 1'b0;
        end
        else begin
            if (en) begin
                // increment count, it overflows to 0
                count <= count + 1'd1;

                // ISO/IEC 14443-2:2016 section 8.2.4
                // The bit period shall start with the loaded state of the carrier
                // so we default to unloaded (0) when not enabled and then as soon
                // as en asserts we toggle the subcarrier high.
                if (count == 0) begin
                    subcarrier = !subcarrier;
                end
            end
            else begin
                count       <= '0;
                subcarrier  <= 1'b0;
            end
        end
    end

    // TODO: Add a check to the tx testbench to make sure that
    //       each bit period starts with the subcarrier in the loaded state

endmodule
