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

    logic [2:0]     bits_in_first_byte;
    logic           append_crc;
    logic [15:0]    crc;

    tx_interface #(.BY_BYTE(0)) in_iface (.*);
    tx_interface #(.BY_BYTE(0)) out_iface (.*);

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    frame_encode dut (.*);

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

    task send_data (logic sq[$]);
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

            // process 2 - actually sends the data
            begin
                tx_source.send_frame(sq);
            end

        // block until both processes finish
        join

        // wait for the expected queue to be empty or timeout
        tx_sink.wait_for_expected_empty(500);

        // wait a few more ticks to make sure nothing more comes through
        repeat (100) @(posedge clk) begin end
    endtask

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin
        automatic logic [7:0] data[$];
        automatic logic       bits[$];
        automatic logic       temp[$];

        fdt_trigger <= 1'b0;
        append_crc  <= 1'b0;

        tx_source.initialise;
        tx_sink.initialise;

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // Stuff to test
        //  1) nothing sends until fdt_trigger fires
        $display("Testing no Tx before fdt");
        tx_sink.clear_expected_queue;  // will assert if out_iface.data_valid asserts
        bits_in_first_byte  <= '0;
        in_iface.data_valid <= 1'b1;
        fdt_trigger         <= 1'b0;
        repeat (100) @(posedge clk) begin end
        in_iface.data_valid <= 1'b0;

        //  2) nothing sends if in_iface.data_valid is low when fdt_trigger fires
        $display("Testing no Tx if in_iface.data_valid not asserted on fdt_trigger");
        tx_sink.clear_expected_queue;  // will assert if out_iface.data_valid asserts
        repeat (5) @(posedge clk) begin end
        fdt_trigger         <= 1'b1;
        @(posedge clk) begin end
        fdt_trigger         <= 1'b0;
        in_iface.data_valid <= 1'b1;
        @(posedge clk) begin end
        in_iface.data_valid <= 1'b0;
        repeat (100) @(posedge clk) begin end

        //  3) parity is correct (number of 1s is odd)
        //      - implicitly checked by adding parity bits to expected queue

        //  4) correct number of bits are sent
        //      - implicity checked by adding all bits to the expected queue

        // send 8 bits of data, no crc
        $display("Testing sending 8 bits");
        data = frame_generator_pkg::generate_byte_queue(1);
        bits = frame_generator_pkg::convert_message_to_bit_queue_for_tx(data);
        temp = frame_generator_pkg::add_parity_to_bit_queue(bits);
        tx_sink.set_expected_queue(temp);
        send_data(bits);

        // send 1 - 8 bits of data, no crc
        for (int i = 1; i <= 8; i++) begin
            $display("Testing sending %d bits", i);
            bits = frame_generator_pkg::generate_bit_queue(i);
            temp = frame_generator_pkg::add_parity_to_bit_queue(bits, i);
            tx_sink.set_expected_queue(temp);

            bits_in_first_byte = 3'(i);
            send_data(bits);
        end

        //  5) multiple bytes send OK
        $display("Testing multi bytes");
        repeat (10000) begin
            automatic int bitsToSend = $urandom_range(9, 100);

            bits_in_first_byte = 3'(bitsToSend % 8);

            //$display("sending %d bits, %d in first byte", bitsToSend, bits_in_first_byte);

            bits = frame_generator_pkg::generate_bit_queue(bitsToSend);
            temp = frame_generator_pkg::add_parity_to_bit_queue(bits, bits_in_first_byte);
            tx_sink.set_expected_queue(temp);

            send_data(bits);
        end

        // 6) Test adding CRC
        // we only care about multiples of 8 bits here
        $display("Test adding CRC");
        bits_in_first_byte  = 3'd0;
        append_crc          = 1'b1;
        repeat (10000) begin
            automatic int bytes_to_send = $urandom_range(1, 10);
            data    = frame_generator_pkg::generate_byte_queue(bytes_to_send);
            crc     = frame_generator_pkg::calculate_crc(data);

            // bit queue to send
            bits    = frame_generator_pkg::convert_message_to_bit_queue_for_tx(data);

            // expected
            data.push_back(crc[7:0]);
            data.push_back(crc[15:8]);
            temp = frame_generator_pkg::convert_message_to_bit_queue_for_tx(data);
            temp = frame_generator_pkg::add_parity_to_bit_queue(temp);
            tx_sink.set_expected_queue(temp);

            send_data(bits);
        end

        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

    // we should assert data_valid on the out_iface 1 tick after the fdt_trigger fires
    validAfterTrigger:
    assert property (
        @(posedge clk)
        ($rose(fdt_trigger) && in_iface.data_valid) |=>
            $rose(out_iface.data_valid))
        else $error("out_iface.data_valid didn't rise after fdt_trigger");

endmodule
