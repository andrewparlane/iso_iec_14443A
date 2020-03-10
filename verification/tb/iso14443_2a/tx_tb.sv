/***********************************************************************
        File: tx_tb.sv
 Description: Testbench for the tx module
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

module tx_tb;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic       clk;
    logic       rst_n;

    tx_interface #(.BY_BYTE(0)) in_iface(.*);

    // the Tx output signal is the manchester encoded data AND'ed with the subcarrier
    logic       tx_out;

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    tx dut (.*);

    // --------------------------------------------------------------
    // The source for the in_iface
    // --------------------------------------------------------------

    tx_interface_source source
    (
        .clk    (clk),
        .iface  (in_iface)
    );

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
    // Functions / Tasks
    // --------------------------------------------------------------

    // our expected data
    logic expected[$];

    // a flag to show when we expect data to be arriving
    logic sending;

    // convert the sendQueue to expected
    task setup_expected_queue (logic sq[$]);
        automatic logic bq [$] = sq;

        // add the SOC bit
        bq.push_front(1'b1);

        //foreach (bq[i]) $display("%b", bq[i]);

        // data is manchester encoded
        //  0 -> 64*0s, 64*1s
        //  1 -> 64*1s, 64*0s
        // and then AND'ed with the subcarrier (fc/16) and starts asserted
        // so in the end:
        //  0: -> 64*0s, repeat 4 times {8*1s, 8*0s}
        //  1: -> repeat 4 times {8*1s, 8*0s}, 64*0s

        expected.delete;
        // it takes 3 ticks to start sending data, so we expect 3 0s to start
        repeat (3) expected.push_back(1'b0);
        foreach (bq[i]) begin
            if (bq[i] == 0) begin
                repeat (64) expected.push_back(1'b0);
            end
            repeat (4) begin
                repeat (8) expected.push_back(1'b1);
                repeat (8) expected.push_back(1'b0);
            end
            if (bq[i] == 1) begin
                repeat (64) expected.push_back(1'b0);
            end
        end

        //$display("expected %p", expected);

        // add two full bit times of unloaded state
        // this confirms nothing extra gets sent out
        repeat (256) expected.push_back(1'b0);
    endtask

    task send_data (logic sq[$]);
        //$display("sending %p", sq);

        // set up the expected queue
        setup_expected_queue(sq);

        // sync to clk edge
        @(posedge clk) begin end

        // send it
        sending <= 1'b1;
        source.send_frame(sq);

        // the tx module doesn't tell us when it's done sending
        // so just wait until the expected queue is empty + a few ticks
        wait (expected.size() == 0) begin end
        repeat (5) @(posedge clk) begin end

        // clear the sending bit
        sending <= 1'b0;

        // wait a couple of ticks
        repeat (5) @(posedge clk) begin end
    endtask

    // --------------------------------------------------------------
    // Output verification
    // --------------------------------------------------------------

    always_ff @(posedge clk) begin: verificationBlock
        if ((expected.size() != 0) && sending) begin: checkingBlock
            automatic logic e = expected.pop_front;
            //$display("got %b", tx_out);
            dataAsExpected:
            assert (tx_out == e) else $error("Expected %b got %b", e, tx_out);
        end
    end

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin
        automatic logic sendQueue[$] = '{};

        sending <= 1'b0;
        source.initialise;

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // Stuff to test
        //  0) SOC - done implicity by adding the SOC to the expected queue
        //  1) nothing sends if send is low
        in_iface.data_valid <= 1'b0;
        expected.delete;
        repeat(512) expected.push_back(1'b0);   // output always 0 for 4 bit times
        repeat (5) @(posedge clk) begin end
        sending <= 1'b1;
        wait (expected.size() == 0) begin end
        @(posedge clk) begin end
        sending <= 1'b0;

        repeat (5) @(posedge clk) begin end

        //  2) correct number of bits are sent
        //      - implicity checked by adding all bits to the expected queue
        //        and by adding 2 bit times of idle to the end of the expected queue

        for (int i = 0; i < 100; i++) begin
            // add a random number of random bits to the sendQueue
            automatic int bits_to_send = $urandom_range(1, 100);
            $display("%d/100 - sending %d bits", i, bits_to_send);
            for (int i = 0; i < bits_to_send; i++) begin
                sendQueue.push_back(1'($urandom));
            end
            send_data(sendQueue);

            repeat (5) @(posedge clk) begin end
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
        !rst_n |-> !tx_out)
        else $error("tx_out should be low in reset");

endmodule
