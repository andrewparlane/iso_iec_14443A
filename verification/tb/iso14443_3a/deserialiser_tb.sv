/***********************************************************************
        File: deserialiser_tb.sv
 Description: Testbench for deserialiser
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

module deserialiser_tb;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic           clk;
    logic           rst_n;

    rx_interface #(.BY_BYTE(0)) in_iface (.*);
    rx_interface #(.BY_BYTE(1)) out_iface (.*);

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    deserialiser dut (.*);

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

    rx_interface_source rx_source
    (
        .clk    (clk),
        .iface  (in_iface)
    );

    // --------------------------------------------------------------
    // The sink for the out_iface
    // --------------------------------------------------------------

    rx_interface_sink rx_sink
    (
        .clk    (clk),
        .iface  (out_iface)
    );

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin
        automatic logic [7:0]   data[$];
        automatic logic         bits[$];

        rx_source.initialise;

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // 1) Test an 8 bit frame
        $display("Testing an 8 bit frame");
        data = frame_generator_pkg::generate_byte_queue(1);
        bits = frame_generator_pkg::convert_message_to_bit_queue_for_rx(data);

        rx_sink.clear_expected_queue;
        rx_sink.build_valid_frame_expected_queue(data);

        rx_source.send_frame(bits);
        rx_sink.wait_for_expected_empty(16);

        // 2) Test 1 - 7 bit frames
        for (int i = 1; i < 8; i++) begin
            $display("Testing a %d bit frame", i);
            data = frame_generator_pkg::generate_byte_queue(1);
            bits = frame_generator_pkg::convert_message_to_bit_queue_for_rx(data, i);

            rx_sink.clear_expected_queue;
            rx_sink.add_expected_soc_event;
            rx_sink.add_expected_eoc_part_byte_event(i, data[0]);

            rx_source.send_frame(bits);
            rx_sink.wait_for_expected_empty(16);
        end

        // 3) send lots of random frames
        $display("Testing lots of frames");
        repeat (1000) begin
            automatic int num_bits              = $urandom_range(1, 80);
            automatic int num_bytes             = int'($ceil(num_bits / 8.0));
            automatic int num_bits_in_last_byte = num_bits % 8;
            automatic logic [7:0] last_byte;

            //$display("Testing a %d bit frame", num_bits);
            data = frame_generator_pkg::generate_byte_queue(num_bytes);
            bits = frame_generator_pkg::convert_message_to_bit_queue_for_rx(data, num_bits_in_last_byte);

            if (num_bits_in_last_byte != 0) begin
                // ends in a partial byte
                last_byte = data.pop_back;
            end

            rx_sink.clear_expected_queue;
            rx_sink.add_expected_soc_event;
            rx_sink.add_expected_data_events(data);
            if (num_bits_in_last_byte == 0) begin
                rx_sink.add_expected_eoc_full_byte_event(1'b0);
            end
            else begin
                rx_sink.add_expected_eoc_part_byte_event(num_bits_in_last_byte, last_byte);
            end

            rx_source.send_frame(bits);
            rx_sink.wait_for_expected_empty(16);
        end

        // 4) send lots of random frames with errors
        $display("Testing frames with errors");
        repeat (1000) begin
            automatic int num_bits              = $urandom_range(1, 80);
            automatic int num_bytes             = int'($ceil(num_bits / 8.0));
            automatic int num_bits_in_last_byte = num_bits % 8;
            automatic int error_before_bit      = $urandom_range(0, num_bits);
            automatic int error_before_byte     = $rtoi(error_before_bit / 8.0);    // $rtoi for truncate not round

            //$display("Testing a %d bit frame with error before bit %d", num_bits, error_before_bit);
            data = frame_generator_pkg::generate_byte_queue(num_bytes);
            bits = frame_generator_pkg::convert_message_to_bit_queue_for_rx(data, num_bits_in_last_byte);

            rx_sink.clear_expected_queue;
            rx_sink.add_expected_soc_event;
            if (error_before_byte != 0) begin
                rx_sink.add_expected_data_events(data[0:error_before_byte-1]);
            end
            if (error_before_bit != num_bits) begin
                rx_sink.add_expected_error_event;
            end
            rx_sink.add_expected_eoc_full_byte_event(error_before_bit == num_bits);

            rx_source.send_frame(bits, 0, error_before_bit);
            rx_sink.wait_for_expected_empty(16);
        end


        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

endmodule
