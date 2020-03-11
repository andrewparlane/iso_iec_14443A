/***********************************************************************
        File: frame_decode_tb.sv
 Description: Testbench for frame_decode
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

module frame_decode_tb;

    import ISO14443A_pkg::*;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic           clk;
    logic           rst_n;

    rx_interface #(.BY_BYTE(0)) in_iface (.*);
    rx_interface #(.BY_BYTE(0)) out_iface (.*);

    logic           last_bit;

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    frame_decode dut (.*);

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

    rx_interface_source source
    (
        .clk    (clk),
        .iface  (in_iface)
    );

    // --------------------------------------------------------------
    // The sink for the out_iface
    // --------------------------------------------------------------

    rx_interface_sink sink
    (
        .clk    (clk),
        .iface  (out_iface)
    );

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------
    logic check_last_bit;

    initial begin
        automatic logic [7:0]   data[$];
        automatic logic         bits[$];

        source.initialise;

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // 1) Test an 8 bit frame with parity bit OK
        //$display("Testing an 8 bit frame with parity bit OK");
        data = frame_generator_pkg::generate_byte_queue(1);
        bits = frame_generator_pkg::convert_message_to_bit_queue(data, 8);

        sink.clear_expected_queue;
        sink.build_valid_frame_expected_queue(bits);

        bits = frame_generator_pkg::add_parity_to_bit_queue(bits);
        check_last_bit = 1'b1;
        source.send_frame(bits);
        sink.wait_for_expected_empty(bits.size * 5 * 2);

        // 2) Test an 8 bit frame with parity FAIL
        //$display("Testing an 8 bit frame with parity FAIL");
        data = frame_generator_pkg::generate_byte_queue(1);
        bits = frame_generator_pkg::convert_message_to_bit_queue(data, 8);

        sink.clear_expected_queue;
        sink.add_expected_soc_event;
        sink.add_expected_data_events(bits);
        sink.add_expected_error_event;
        sink.add_expected_eoc_full_byte_event(1'b0);

        bits = frame_generator_pkg::add_parity_to_bit_queue(bits);
        bits[$] = !bits[$]; // flip the parity bit

        source.send_frame(bits);
        check_last_bit = 1'b0;
        sink.wait_for_expected_empty(bits.size * 5 * 2);

        // 3) Test an 8 bit frame with parity missing
        //$display("Testing an 8 bit frame with parity bit missing");
        data = frame_generator_pkg::generate_byte_queue(1);
        bits = frame_generator_pkg::convert_message_to_bit_queue(data, 8);
        sink.clear_expected_queue;
        sink.add_expected_soc_event;
        sink.add_expected_data_events(bits);
        sink.add_expected_eoc_full_byte_event(1'b1);

        // don't add parity bit

        source.send_frame(bits);
        check_last_bit = 1'b1;
        sink.wait_for_expected_empty(bits.size * 5 * 2);

        // 4) Test an 8 bit frame + parity with error in each location
        //      before bit 0, bit 1, ... bit 8, bit 9, EOC

        for (int i = 0; i < 10; i++) begin
            //$display("Testing an 8 bit frame with an error at idx %d", i);

            data = frame_generator_pkg::generate_byte_queue(1);
            bits = frame_generator_pkg::convert_message_to_bit_queue(data, 8);

            sink.clear_expected_queue;
            sink.add_expected_soc_event;
            if (i != 0) begin
                sink.add_expected_data_events(bits[0:(i < 8) ? i-1 : 7]);
            end
            if (i != 9) begin
                sink.add_expected_error_event;
            end
            sink.add_expected_eoc_full_byte_event(i == 9);

            bits = frame_generator_pkg::add_parity_to_bit_queue(bits);
            check_last_bit = 1'b0;
            source.send_frame(bits, 0, i);
            sink.wait_for_expected_empty(bits.size * 5 * 2);
        end

        // 5) Test a 0 bit frame
        //$display("Testing a 0 bit frame");
        sink.clear_expected_queue;
        sink.add_expected_soc_event;
        sink.add_expected_eoc_full_byte_event(1'b1);

        check_last_bit = 1'b0;
        source.send_frame('{});
        sink.wait_for_expected_empty(100);

        // 6) test 1 - 7 bit frames
        for (int bitLen = 1; bitLen <= 7; bitLen++) begin
            //$display("Testing a %d bit frame", bitLen);
            data = frame_generator_pkg::generate_byte_queue(1);
            bits = frame_generator_pkg::convert_message_to_bit_queue(data, bitLen);

            sink.clear_expected_queue;
            sink.build_valid_frame_expected_queue(bits);

            check_last_bit = 1'b1;
            source.send_frame(bits);
            sink.wait_for_expected_empty(bits.size * 5 * 2);
        end

        // repeat these tests a bunch of times
        repeat (1000) begin
            // 1 - 1000 bits (range is a bit arbitrary, but should be good enough)
            automatic int       num_bits                = $urandom_range(1, 1000);
            automatic int       num_bytes               = int'($ceil(num_bits / 8.0));
            automatic int       num_bits_in_last_byte   = num_bits % 8;

            // 7) Test an N bit frame with parity OK
            //$display("Testing a %d bit frame with parity bits OK", num_bits);
            data = frame_generator_pkg::generate_byte_queue(num_bytes);
            bits = frame_generator_pkg::convert_message_to_bit_queue(data, num_bits_in_last_byte);

            sink.clear_expected_queue;
            sink.build_valid_frame_expected_queue(bits);

            bits = frame_generator_pkg::add_parity_to_bit_queue(bits);
            check_last_bit = 1'b1;
            source.send_frame(bits);
            sink.wait_for_expected_empty(bits.size * 5 * 2);

            // 8) Test an N bit frame with parity FAIL
            if (num_bits > 8) begin
                automatic int broken_parity_byte    = $urandom_range(num_bytes - 2);
                //$display("Testing a %d bit frame with broken parity bit in byte %d", num_bits, broken_parity_byte);
                data = frame_generator_pkg::generate_byte_queue(num_bytes);

                bits = frame_generator_pkg::convert_message_to_bit_queue(data, num_bits_in_last_byte);

                sink.clear_expected_queue;
                sink.add_expected_soc_event;
                sink.add_expected_data_events(bits[0:broken_parity_byte*8 + 7]);
                sink.add_expected_error_event;
                sink.add_expected_eoc_full_byte_event(1'b0);

                bits = frame_generator_pkg::add_parity_to_bit_queue(bits);
                bits[broken_parity_byte*9 + 8] = !bits[broken_parity_byte*9 + 8]; // break the parity bit
                check_last_bit = 1'b0;
                source.send_frame(bits);
                sink.wait_for_expected_empty(bits.size * 5 * 2);
            end

            // 9) Test an N byte frame with last parity missing
            num_bytes = $urandom_range(1, 100);
            //$display("Testing a %d byte frame with last parity missing", num_bytes);
            data = frame_generator_pkg::generate_byte_queue(num_bytes);
            bits = frame_generator_pkg::convert_message_to_bit_queue(data, 8);

            // expecting parity error on EOC
            sink.clear_expected_queue;
            sink.add_expected_soc_event;
            sink.add_expected_data_events(bits);
            sink.add_expected_eoc_full_byte_event(1'b1);

            bits = frame_generator_pkg::add_parity_to_bit_queue(bits);
            void'(bits.pop_back);   // remove the last bit

            check_last_bit = 1'b1;
            source.send_frame(bits);
            sink.wait_for_expected_empty(bits.size * 5 * 2);
        end

        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

    // check last_bit is correct on eoc rising
    lastBitCorrect:
    assert property (
        @(posedge clk)
        ($rose(out_iface.eoc) && check_last_bit) |=>
            (last_bit == in_iface.data))
        else $error("last_bit is %b, expected %b", last_bit, in_iface.data);

    // last_bit can't change after eoc until after the next soc
    lastBitStableBetweenFrames:
    assert property (
        @(posedge clk)
        $rose(out_iface.eoc) |=> $stable(last_bit) throughout out_iface.soc[->1])
        else $error("last_bit changed between frames");

endmodule
