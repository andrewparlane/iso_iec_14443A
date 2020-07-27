/***********************************************************************
        File: subcarrier_tb.sv
 Description: Testbench for subcarrier
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

module subcarrier_tb;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic           clk;
    logic           rst_n;

    logic           en;
    logic           subcarrier;

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    subcarrier dut (.*);

    // --------------------------------------------------------------
    // Clock generator
    // --------------------------------------------------------------

    // Calculate our clock period in ps
    localparam CLOCK_FREQ_HZ = 13560000; // 13.56MHz
    localparam CLOCK_PERIOD_PS = 1000000000000.0 / CLOCK_FREQ_HZ;
    initial begin
        clk = 1'b0;
        forever begin
            #(int'(CLOCK_PERIOD_PS/2))
            clk = ~clk;
        end
    end

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin
        en <= 1'b0;

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // enable for 2 bit times
        en <= 1'b1;
        repeat (256) @(posedge clk) begin end
        en <= 1'b0;

        repeat (50) @(posedge clk) begin end

        // enable for 6 ticks (should disable while high)
        en <= 1'b1;
        repeat (6) @(posedge clk) begin end
        en <= 1'b0;

        // enable for 13 ticks (should disable while low)
        en <= 1'b1;
        repeat (13) @(posedge clk) begin end
        en <= 1'b0;

        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

    inReset:
    assert property (
        @(posedge clk)
        !rst_n |-> !subcarrier)
        else $error("subcarrier should be low in reset");

    notEnabled:
    assert property (
        @(posedge clk)
        !en |=> !subcarrier)
        else $error("subcarrier should be low whilst not enabled");

    // ISO/IEC 14443-2:2016 section 8.2.4
    // The bit period shall start with the loaded state of the carrier
    enabling:
    assert property (
        @(posedge clk)
        $rose(en) |=> subcarrier)
        else $error("en rose but subcarrier remained low");

    // synopsys doesn't like disable iff (!en)
    logic notEn;
    assign notEn = !en;

    correctPeriod:
    assert property (
        @(posedge clk)
        disable iff (notEn)
        $rose(subcarrier) |=>
                    $stable(subcarrier)[*7]
            ##1     $fell(subcarrier)
            ##1     $stable(subcarrier)[*7]
            ##1     $rose(subcarrier))
        else $error("subcarrier waveform not as expected");

endmodule
