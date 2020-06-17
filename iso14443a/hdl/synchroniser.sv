/***********************************************************************
        File: synchroniser.sv
 Description: Synchroniser for async signals
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

// SDC: set_false_path

module synchroniser
#(
    parameter               WIDTH       = 1,
    parameter [WIDTH-1:0]   RESET_VAL   = '0
)
(
    input                       clk,
    input                       rst_n,
    input           [WIDTH-1:0] d,
    output logic    [WIDTH-1:0] q
);

    logic [WIDTH-1:0] tmp;

    always @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            tmp <= RESET_VAL;
            q   <= RESET_VAL;
        end
        else begin
            q   <= tmp;
            tmp <= d;
        end
    end

endmodule
