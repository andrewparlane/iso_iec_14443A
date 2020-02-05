/***********************************************************************
        File: fdt_tb.sv
 Description: Testbench for the fdt module
      Author: Andrew Parlane
************************************************************************/

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

module fdt_tb;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic   clk;
    logic   rst_n;

    logic   pause_n_synchronised;
    logic   last_rx_bit;
    logic   trigger;

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    localparam int TIMING_ADJUST = 13;

    fdt
    #(
        .TIMING_ADJUST (TIMING_ADJUST)
    )
    dut (.*);

    // --------------------------------------------------------------
    // Clock generator
    // --------------------------------------------------------------

    // use a 100MHz clock here, it makes the timing calculations easier
    // and doesn't affect the functionality
    // Calculate our clock period in ps
    localparam CLOCK_FREQ_HZ = 100000000; // 100MHz
    localparam CLOCK_PERIOD_PS = 1000000000000.0 / CLOCK_FREQ_HZ;
    initial begin
        clk = 1'b0;
        forever begin
            #(int'(CLOCK_PERIOD_PS/2))
            clk = ~clk;
        end
    end

    // --------------------------------------------------------------
    // Event detector
    // --------------------------------------------------------------

    // Timings, from ISO/IEC 14443-3:2016 section 6.2.1.1
    localparam int FDT_LAST_BIT_0 = 1172 - TIMING_ADJUST;
    localparam int FDT_LAST_BIT_1 = 1236 - TIMING_ADJUST;

    // this is a time in ps (`timescale)
    longint lastPauseRise;
    always_ff @(posedge pause_n_synchronised) lastPauseRise <= $time;

    always_ff @(posedge trigger) begin: triggerBlock
        // trigger has fired
        automatic longint diff = $time - lastPauseRise;
        automatic longint expected = CLOCK_PERIOD_PS * (last_rx_bit ? FDT_LAST_BIT_1 : FDT_LAST_BIT_0);
        //$display("Trigger event at %d ps, lastPauseRise %d ps, diff %d, expected %d", $time, lastPauseRise, diff, expected);

        fdtTime: assert (diff == expected)
            else $error("Trigger event at %d ps, lastPauseRise %d ps, diff %d, expected %d",
                        $time, lastPauseRise, diff, expected);
    end

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    task timeout (output bit timedout);
        timedout <= 1'b0;
        fork
            // process 1, wait for the trigger
            begin
                wait (trigger) begin end
            end

            // process 2, timeout after 3000 ticks
            // we use 3000 because the counter in the dut is 11 bits wide
            // so it will wrap every 2048 ticks (if left free running)
            begin
                repeat (3000) @(posedge clk) begin end
                timedout <= 1'b1;
            end
        // finish as soon as any of these processes finish
        join_any

        // disable the remaining process
        disable fork;

        // wait a little bit to make sure the trigger is still not asserted
        repeat (5) @(posedge clk) begin end
    endtask

    initial begin: testStimulus
        automatic bit timedout;
        pause_n_synchronised <= 1'b1;

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // make sure nothing happens before we get a pause
        timeout(timedout);
        expectTimeOut1: assert (timedout) else $error("Didn't timeout when expected");

        // Test last_bit 0
        last_rx_bit             <= 1'b0;
        pause_n_synchronised    <= 1'b0;
        repeat (5) @(posedge clk) begin end
        pause_n_synchronised    <= 1'b1;

        // wait for the trigger
        timeout(timedout);
        expectNotTimeOut1: assert (!timedout) else $error("Timedout when expecting trigger");

        // make sure nothing happens before we get the next pause
        timeout(timedout);
        expectTimeOut2: assert (timedout) else $error("Didn't timeout when expected");

        // Test last_bit 1
        last_rx_bit             <= 1'b1;
        pause_n_synchronised    <= 1'b0;
        repeat (5) @(posedge clk) begin end
        pause_n_synchronised    <= 1'b1;

        // wait for the trigger
        timeout(timedout);
        expectNotTimeOut2: assert (!timedout) else $error("Timedout when expecting trigger");

        // Test multiple pauses
        repeat (1000) begin: randomTests
            automatic int num_pauses = $urandom_range(1, 5);
            repeat (num_pauses) begin
                // delay between pauses
                automatic int ticks_between_pause = $urandom_range(1, 1000);
                repeat (ticks_between_pause) @(posedge clk) begin end

                // the pause
                pause_n_synchronised    <= 1'b0;
                repeat (5) @(posedge clk) begin end
                pause_n_synchronised    <= 1'b1;

                // randomize last_bit
                last_rx_bit <= 1'($urandom);
            end

            // wait for the trigger
            timeout(timedout);
            expectNotTimeOut3: assert (!timedout) else $error("Timedout when expecting trigger");
        end

        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

    inReset:
    assert property (
        @(posedge clk)
        !rst_n |-> !trigger)
        else $error("subcarrier should be low in reset");


endmodule
