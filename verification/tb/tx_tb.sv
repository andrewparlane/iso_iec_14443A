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

    logic       fdt_trigger;

    logic [7:0] data;
    logic [2:0] data_bits;
    logic       ready_to_send;

    logic       req;

    // the Tx output signal is the manchester encoded data AND'ed with the subcarrier
    logic       tx;

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    tx dut (.*);

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

    typedef struct
    {
        int         bits;
        bit [7:0]   data;
    } SendByteInfo;

    // our expected data
    bit expected[$];

    // a flag to show when we expect data to be arriving
    logic sending;

    // convert the sendQueue to expected
    task setup_expected_queue (SendByteInfo sq[$]);
        automatic bit bq [$] = '{};

        // add the SOC bit
        bq.push_back(1'b1);

        // convert the SendByteInfo queue to a bit stream
        foreach (sq[i]) begin
            automatic bit [7:0] dataByte = sq[i].data;

            // Data is expected LSb first
            automatic int j;
            for (j = 0; j < sq[i].bits; j++) begin
                bq.push_back(dataByte[j]);
            end

            // clear unused bits for parity calculation purposes
            // j = j to hide linter warning about for loop without initializer
            for (j = j; j < 8; j++) begin
                dataByte[j] = 1'b0;
            end

            // add the parity
            bq.push_back(bit'(($countones(dataByte) % 2) == 0));
        end

        //foreach (bq[i]) $display("%b", bq[i]);

        // data is manchester encoded
        //  0 -> 64*0s, 64*1s
        //  1 -> 64*1s, 64*0s
        // and then AND'ed with the subcarrier (fc/16) and starts asserted
        // so in the end:
        //  0: -> 64*0s, repeat 4 times {8*1s, 8*0s}
        //  1: -> repeat 4 times {8*1s, 8*0s}, 64*0s

        expected.delete;
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

        // add two full bit times of unloaded state
        // this confirms nothing extra gets sent out
        repeat (256) expected.push_back(1'b0);
    endtask

    task send_data (SendByteInfo sq[$]);
        // set up the expected queue
        setup_expected_queue(sq);

        fork

            // process 1 - fires the fdt trigger
            begin
                automatic int ticksBeforeFDT = $urandom_range(5, 100);
                repeat (ticksBeforeFDT) @(posedge clk) begin end
                fdt_trigger <= 1'b1;
                @(posedge clk) begin end    // after 1 tick, state changes to State_SOC
                fdt_trigger <= 1'b0;
                @(posedge clk) begin end    // after 2 ticks enable is registered
                                            // after 3 ticks data is on the wire
                // we set sending here after 2 ticks
                // because it takes one tick for the verification block to see it
                sending     <= 1'b1;
            end

            // process 2 - actually sends the data (waits for req and provides next bytes)
            begin
                foreach (sq[i]) begin
                    // set up the inputs
                    data                = sq[i].data;
                    data_bits           = (sq[i].bits == 8) ? 3'd0 : 3'(sq[i].bits);
                    ready_to_send       = 1'b1;

                    // wait a tick so req isn't asserted still
                    @(posedge clk)

                    // wait for the next req, and align to the clock
                    wait (req) begin end
                    @(posedge clk) begin end
                end

                // nothing more to send, clear ready_to_send
                ready_to_send = 1'b0;
            end

        // block until both processes finish
        join

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
            automatic bit e = expected.pop_front;
            dataAsExpected:
            assert (tx == e) else $error("Expected %b got %b", e, tx);
        end
    end

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin
        automatic SendByteInfo sendQueue[$] = '{};

        ready_to_send   <= 1'b0;
        fdt_trigger     <= 1'b0;

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // Stuff to test
        //  0) SOC - done implicity by adding the SOC to the expected queue

        //  1) nothing sends until fdt_trigger fires
        data            <= 8'hA5;
        data_bits       <= 3'd2;
        ready_to_send   <= 1'b1;
        fdt_trigger     <= 1'b0;
        expected.delete;
        repeat(512) expected.push_back(1'b0);   // output always 0 for 4 bit times
        sending         <= 1'b1;
        wait (expected.size() == 0) begin end
        @(posedge clk) begin end
        sending         <= 1'b0;

        //  2) nothing sends if ready_to_send is low when fdt_trigger fires
        ready_to_send   <= 1'b0;
        expected.delete;
        repeat(512) expected.push_back(1'b0);   // output always 0 for 4 bit times
        repeat (5) @(posedge clk) begin end
        fdt_trigger     <= 1'b1;
        @(posedge clk) begin end
        fdt_trigger     <= 1'b0;
        sending         <= 1'b1;
        wait (expected.size() == 0) begin end
        @(posedge clk) begin end
        sending         <= 1'b0;

        //  3) parity is correct (number of 1s is odd)
        //      - implicitly checked by adding parity bits to expected queue

        //  4) correct number of bits are sent
        //      - implicity checked by adding all bits to the expected queue
        //        and by adding 2 bit times of idle to the end of the expected queue

        // send every possible combination of 1-8 bits
        for (int bits = 1; bits <= 8; bits++) begin
            for (int dts = 0; dts <= ((2**bits)-1); dts++) begin
                // randomize the none used bits, to make sure that doesn't affect things
                automatic bit [7:0] d = 8'(($urandom() & ~((2**bits)-1)) | dts);
                //$display("sending %d bits: %h", bits, d);
                send_data ('{'{bits, d}});
            end
        end

        //  5) multiple bytes send OK (don't have to be full bytes)

        repeat (10000) begin
            automatic int bytesToSend = $urandom_range(2, 10);
            automatic SendByteInfo sq[$] = '{};
            //$display("sending %d bytes", bytesToSend);

            for (int i = 0; i < bytesToSend; i++) begin
                automatic int bitsToSend = $urandom_range(1,8);
                automatic bit [7:0] dataToSend = 8'($urandom());
                //$display("  %d bits: %h", bitsToSend, dataToSend);

                sq.push_back('{bitsToSend, dataToSend});
            end

            send_data(sq);
        end

        //  6) LSb sent first - implicit in that we add the data to the expected queue LSb first

        // TODO: confirm my understanding of Tx behaviour is correct. How?
        //       Maybe look at Fabricio's testbenches? and see if the bit streams match?

        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

    inReset:
    assert property (
        @(posedge clk)
        !rst_n |-> (!req && !tx))
        else $error("subcarrier should be low in reset");

endmodule
