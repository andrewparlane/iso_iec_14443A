/***********************************************************************
        File: frame_encode_tb.sv
 Description: Testbench for the frame_encode module
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

module frame_encode_tb;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic           clk;
    logic           rst_n;

    logic           fdt_trigger;

    // Input data
    logic           in_data;
    logic           in_valid;
    logic           in_req;

    logic [2:0]     bits_in_first_byte;
    logic           append_crc;
    logic [15:0]    crc;

    // Output data
    logic           out_data;
    logic           out_valid;
    logic           out_req;

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    frame_encode dut (.*);

    // --------------------------------------------------------------
    // PICC -> PCD clock and comms generator
    // --------------------------------------------------------------
    // used to generate the clock and data, but not to send it
    iso14443a_pcd_to_picc_comms_generator bfm
    (
        .clk            (clk),
        .pcd_pause_n    (),
        .pause_n        (),
        .sending        ()
    );

    // --------------------------------------------------------------
    // Functions / Tasks
    // --------------------------------------------------------------

    // our expected data
    bit expected[$];

    task send_data (bit sq[$]);
        // sync to clock edge
        @(posedge clk)

        fork

            // process 1 - fires the fdt trigger
            begin
                automatic int ticksBeforeFDT = $urandom_range(5, 100);
                repeat (ticksBeforeFDT) @(posedge clk) begin end
                fdt_trigger <= 1'b1;
                @(posedge clk) begin end
                fdt_trigger <= 1'b0;
            end

            // process 2 - actually sends the data (waits for req and provides next bytes)
            begin
                foreach (sq[i]) begin
                    // set up the inputs
                    in_data         <= sq[i];
                    in_valid        <= 1'b1;

                    //$display("sending %b", sq[i]);

                    // wait a tick so req isn't asserted still
                    @(posedge clk)

                    // wait for the next req, and align to the clock
                    wait (in_req) begin end
                    @(posedge clk) begin end
                end

                // nothing more to send, clear in_valid
                in_valid <= 1'b0;
            end

        // block until both processes finish
        join

        // wait for the expected queue to be empty or timeout

        fork
            // process 1 - wait for expected queue to be empty
            begin
                // the tx module doesn't tell us when it's done sending
                // so just wait until the expected queue is empty + a few ticks
                wait (expected.size() == 0) begin end
            end

            // process 2 - wait for timeout
            begin
                // after we finish sending, the DUT has to continue sending
                // 16 CRC bits + 3 parity bits
                // we issue out_req every 6 cycles, so should take ~114 cycles
                // timeout after 500
                repeat (500) @(posedge clk) begin end
            end
        join_any

        timeout:
        assert (expected.size() == 0) else $error("Timed out waiting for expected queue to empty");

        // wait a few more ticks to make sure nothing more comes through
        repeat (100) @(posedge clk) begin end
    endtask

    // --------------------------------------------------------------
    // Deal with the output signals
    // --------------------------------------------------------------

    initial begin
        out_req <= 1'b0;

        forever begin
            // wait for the out_valid to assert
            wait (out_valid) begin end

            // 4 ticks later request more data
            repeat(4) @(posedge clk) begin end

            out_req <= 1'b1;
            @(posedge clk) begin end
            out_req <= 1'b0;
            @(posedge clk) begin end
        end
    end

    // --------------------------------------------------------------
    // Output verification
    // --------------------------------------------------------------

    always_ff @(posedge clk) begin: verificationBlock
        if (out_req) begin
            expectedNotEmpty:
            assert(expected.size() != 0) else $error("expected queue empty, but received data");

            //$display("got: %b", out_data);

            if ((expected.size() != 0)) begin: checkingBlock
                automatic bit e = expected.pop_front;
                dataAsExpected:
                assert (out_data == e) else $error("Expected %b got %b", e, out_data);
            end
        end
    end

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin
        automatic bit [7:0] data[$];
        automatic bit       bits[$];

        fdt_trigger <= 1'b0;
        in_valid    <= 1'b0;
        append_crc  <= 1'b0;

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // Stuff to test
        //  1) nothing sends until fdt_trigger fires
        $display("Testing no Tx before fdt");
        expected.delete;    // will assert if out_valid asserts
        in_data             <= 1'b0;
        bits_in_first_byte  <= '0;
        in_valid            <= 1'b1;
        fdt_trigger         <= 1'b0;
        repeat (100) @(posedge clk) begin end
        in_valid            <= 1'b0;

        //  2) nothing sends if in_valid is low when fdt_trigger fires
        $display("Testing no Tx if in_valid not asserted on fdt_trigger");
        expected.delete;
        repeat (5) @(posedge clk) begin end
        fdt_trigger     <= 1'b1;
        @(posedge clk) begin end
        fdt_trigger     <= 1'b0;
        in_valid        <= 1'b1;
        @(posedge clk) begin end
        in_valid        <= 1'b0;
        repeat (100) @(posedge clk) begin end

        //  3) parity is correct (number of 1s is odd)
        //      - implicitly checked by adding parity bits to expected queue

        //  4) correct number of bits are sent
        //      - implicity checked by adding all bits to the expected queue

        // send 8 bits of data, no crc
        $display("Testing sending 8 bits");
        data        = bfm.generate_byte_queue(1);
        bits        = bfm.convert_message_to_bit_queue(data, 8);
        expected    = bfm.add_parity_to_bit_queue(bits);
        send_data(bits);

        // send 1 - 8 bits of data, no crc
        for (int i = 1; i <= 8; i++) begin
            $display("Testing sending %d bits", i);
            bits        = bfm.generate_bit_queue(i);
            expected    = bfm.add_parity_to_bit_queue(bits, i);

            bits_in_first_byte = 3'(i);
            send_data(bits);
        end

        //  5) multiple bytes send OK
        $display("Testing multi bytes");
        repeat (10000) begin
            automatic int bitsToSend = $urandom_range(9, 100);

            bits_in_first_byte = 3'(bitsToSend % 8);

            //$display("sending %d bits, %d in first byte", bitsToSend, bits_in_first_byte);

            bits        = bfm.generate_bit_queue(bitsToSend);
            expected    = bfm.add_parity_to_bit_queue(bits, bits_in_first_byte);

            send_data(bits);
        end

        // 6) Test adding CRC
        // we only care about multiples of 8 bits here
        $display("Test adding CRC");
        bits_in_first_byte  = 3'd0;
        append_crc          = 1'b1;
        repeat (10000) begin
            automatic int bytes_to_send = $urandom_range(1, 10);
            data        = bfm.generate_byte_queue(bytes_to_send);
            crc         = bfm.calculate_crc(data);

            // bit queue to send
            bits        = bfm.convert_message_to_bit_queue(data, 8);

            // expected
            data.push_back(crc[7:0]);
            data.push_back(crc[15:8]);
            expected    = bfm.add_parity_to_bit_queue(bfm.convert_message_to_bit_queue(data, 8));

            send_data(bits);
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
        !rst_n |-> (!out_valid && !in_req))
        else $error("Invalid outputs in reset");

endmodule
