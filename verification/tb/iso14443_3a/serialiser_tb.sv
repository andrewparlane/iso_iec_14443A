/***********************************************************************
        File: serialiser_tb.sv
 Description: Testbench for serialiser
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

module serialiser_tb;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic           clk;
    logic           rst_n;

    tx_interface #(.BY_BYTE(1)) in_iface (.*);
    tx_interface #(.BY_BYTE(0)) out_iface (.*);

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    serialiser dut (.*);

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
    // The source for the in_iface
    // --------------------------------------------------------------

    tx_interface_source tx_source
    (
        .clk    (clk),
        .iface  (in_iface)
    );

    // --------------------------------------------------------------
    // The sink for the out_iface
    // --------------------------------------------------------------

    tx_interface_sink tx_sink
    (
        .clk    (clk),
        .iface  (out_iface)
    );

    // --------------------------------------------------------------
    // Tasks
    // --------------------------------------------------------------

    task send_frame (int num_bits);
        automatic logic [7:0]   data                [$];
        automatic logic         expected            [$];
        automatic logic         last_bit_expected   [$];
        automatic const int     num_bytes           = int'($ceil(num_bits / 8.0));
        automatic const int     bits_in_first_byte  = num_bits % 8;
        automatic const int     num_zeros           = (bits_in_first_byte == 0) ? 7 : bits_in_first_byte - 1'd1;

        // generate the data and expected queue (bit stream)
        data        = frame_generator_pkg::generate_byte_queue(num_bytes);
        expected    = frame_generator_pkg::convert_message_to_bit_queue_for_tx(data, bits_in_first_byte);

        // generate the last_bit_expected queue
        // we expect the first last_bit to come based on bits_in_first_byte
        repeat(num_zeros) last_bit_expected.push_back(1'b0);
        last_bit_expected.push_back(1'b1);
        // then every 8 bits after that
        repeat (num_bytes - 1) begin
            repeat(7) last_bit_expected.push_back(1'b0);
            last_bit_expected.push_back(1'b1);
        end

        // set the expected queues
        tx_sink.set_expected_queue(expected, last_bit_expected);

        // send it
        tx_source.send_frame(data, bits_in_first_byte);

        // wait for us to receive it in the sink
        tx_sink.wait_for_expected_empty(16);

        // wait a few more ticks
        repeat (5) @(posedge clk) begin end
    endtask

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin
        tx_source.initialise;
        tx_sink.initialise;

        tx_sink.enable_expected_checking(1'b1, 1'b1);

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // 1) Test an 8 bit frame
        $display("Testing an 8 bit frame");
        send_frame(8);

        // 2) Test 1 - 7 bit frames
        for (int i = 1; i < 8; i++) begin
            $display("Testing a %d bit frame", i);
            send_frame(i);
        end

        // 3) send lots of random frames
        $display("Testing lots of frames");
        repeat (1000) begin
            send_frame($urandom_range(1, 80));
        end

        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

endmodule
