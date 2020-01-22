/***********************************************************************
        File: seven_seg_hex.sv
 Description: Output hex values to a seven segment display
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

module seven_seg_hex
(
    input                   clk,
    input                   rst_n,
    input                   en,
    input           [3:0]   hex,
    output logic    [6:0]   display
);

    logic [6:0] displayAux;

    // All active low
    //
    //         0
    //      -------
    //      |     |
    //    5 |     | 1
    //      |  6  |
    //      -------
    //      |     |
    //    4 |     | 2
    //      |     |
    //      -------
    //         3

    always_comb begin
        case (hex)
            4'h0:       displayAux = 7'b0111111;
            4'h1:       displayAux = 7'b0000110;
            4'h2:       displayAux = 7'b1011011;
            4'h3:       displayAux = 7'b1001111;
            4'h4:       displayAux = 7'b1100110;
            4'h5:       displayAux = 7'b1101101;
            4'h6:       displayAux = 7'b1111101;
            4'h7:       displayAux = 7'b0000111;
            4'h8:       displayAux = 7'b1111111;
            4'h9:       displayAux = 7'b1101111;
            4'hA:       displayAux = 7'b1110111;
            4'hB:       displayAux = 7'b1111100;
            4'hC:       displayAux = 7'b1011000;
            4'hD:       displayAux = 7'b1011110;
            4'hE:       displayAux = 7'b1111001;
            4'hF:       displayAux = 7'b1110001;
            default:    displayAux = 7'b0000000;    // all off
        endcase
    end

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            display <= '1; // off
        end
        else begin
            if (en) begin
                display <= ~displayAux;
            end
            else begin
                display <= '1; // off
            end
        end
    end

endmodule
