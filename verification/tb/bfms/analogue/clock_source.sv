/***********************************************************************
        File: clock_source.sv
 Description: Generates a clock
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

module clock_source
#(
    // The half period is rounded to the nearest ps
    // so the resulting clock not perfectly 13.56MHz
    parameter CLOCK_FREQ_HZ = 13560000  // 13.56MHz
)
(
    output logic clk
);

    // Calculate our clock period in ps
    localparam real CLOCK_PERIOD_PS = 1000000000000.0 / CLOCK_FREQ_HZ;

    initial begin
        clk <= 1'b0;
        forever begin
            #(int'(CLOCK_PERIOD_PS/2))
            clk <= !clk;
        end
    end

endmodule
