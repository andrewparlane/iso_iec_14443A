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

    logic           sd_soc;
    logic           sd_eoc;
    logic           sd_data;
    logic           sd_data_valid;
    logic           sd_error;

    logic           soc;
    logic           eoc;
    logic           data;
    logic           data_valid;
    logic           error;
    logic           last_bit;

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    frame_decode dut (.*);

    // --------------------------------------------------------------
    // PICC -> PCD clock and comms generator
    // Note: we only use this to generate data, not to send it
    // --------------------------------------------------------------
    iso14443a_pcd_to_picc_comms_generator bfm
    (
        .clk            (clk),
        .pcd_pause_n    (),
        .pause_n        (),
        .sending        ()
    );

    // --------------------------------------------------------------
    // Verify results are as expected
    // --------------------------------------------------------------

    frame_decode_validator fd_validator (.*);

    // --------------------------------------------------------------
    // Task to send sequence queues
    // --------------------------------------------------------------

    task send_frame (bit sq[$], int error_before_bit=-1);
        automatic logic expectedEmpty;
        automatic logic errorSent = 1'b0;

        // SOC
        sd_soc <= 1'd1;
        @(posedge clk)
        sd_soc <= 1'd0;

        foreach (sq[i]) begin
            repeat (5) @(posedge clk) begin end // sync to clock edge and delay between bits

            if (error_before_bit == i) begin
                sd_error    <= 1'b1;
                @(posedge clk)
                sd_error    <= 1'b0;
                repeat (5) @(posedge clk) begin end

                errorSent   = 1'b1;
            end

            sd_data         <= sq[i];
            sd_data_valid   <= 1'b1;
            @(posedge clk)
            sd_data_valid   <= 1'b0;
        end

        repeat (5) @(posedge clk) begin end

        if ((error_before_bit != -1) && !errorSent) begin
            // send the error on the EOC
            sd_error    <= 1'b1;
        end

        sd_eoc      <= 1'b1;
        @(posedge clk)
        sd_eoc      <= 1'b0;
        sd_error    <= 1'b0;

        repeat (5) @(posedge clk) begin end

        expectedEmpty = fd_validator.expected_queue_is_empty();
        expectedQueueEmpty: assert (expectedEmpty) else $error("Finished sending but still expected data");
    endtask


    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin
        automatic bit [7:0] data[$];
        automatic bit       bits[$];

        sd_soc          = 1'b0;
        sd_eoc          = 1'b0;
        sd_error        = 1'b0;
        sd_data_valid   = 1'b0;

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // 1) Test an 8 bit frame with parity bit OK
        //$display("Testing an 8 bit frame with parity bit OK");
        data = bfm.generate_byte_queue(1);
        bits = bfm.convert_message_to_bit_queue(data, 8);

        fd_validator.clear_expected_queue;
        fd_validator.push_soc_event;
        fd_validator.push_data_events(bits);
        fd_validator.push_eoc_event(1'b0);

        bits = bfm.add_parity_to_bit_queue(bits);
        send_frame(bits);

        // 2) Test an 8 bit frame with parity FAIL
        //$display("Testing an 8 bit frame with parity FAIL");
        data = bfm.generate_byte_queue(1);
        bits = bfm.convert_message_to_bit_queue(data, 8);

        fd_validator.clear_expected_queue;
        fd_validator.push_soc_event;
        fd_validator.push_data_events(bits);
        fd_validator.push_error_event;
        fd_validator.push_eoc_event(1'b0);

        bits = bfm.add_parity_to_bit_queue(bits);
        bits[$] = !bits[$]; // flip the parity bit

        send_frame(bits);

        // 3) Test an 8 bit frame with parity missing
        //$display("Testing an 8 bit frame with parity bit missing");
        data = bfm.generate_byte_queue(1);
        bits = bfm.convert_message_to_bit_queue(data, 8);
        fd_validator.clear_expected_queue;
        fd_validator.push_soc_event;
        fd_validator.push_data_events(bits);
        fd_validator.push_eoc_event(1'b1);

        // don't add parity bit

        send_frame(bits);

        // 4) Test an 8 bit frame + parity with error in each location
        //      before bit 0, bit 1, ... bit 8, bit 9, EOC

        for (int i = 0; i < 10; i++) begin
            //$display("Testing an 8 bit frame with an error at idx %d", i);

            data = bfm.generate_byte_queue(1);
            bits = bfm.convert_message_to_bit_queue(data, 8);

            fd_validator.clear_expected_queue;
            fd_validator.push_soc_event;
            if (i != 0) begin
                fd_validator.push_data_events(bits[0:(i < 8) ? i-1 : 7]);
            end
            if (i != 9) begin
                fd_validator.push_error_event;
            end
            fd_validator.push_eoc_event(i == 9);

            bits = bfm.add_parity_to_bit_queue(bits);
            send_frame(bits, i);
        end

        // 5) Test a 0 bit frame
        //$display("Testing a 0 bit frame");
        fd_validator.clear_expected_queue;
        fd_validator.push_soc_event;
        fd_validator.push_eoc_event(1'b1);

        send_frame('{});

        // 6) test 1 - 7 bit frames
        for (int bitLen = 1; bitLen <= 7; bitLen++) begin
            //$display("Testing a %d bit frame", bitLen);
            data = bfm.generate_byte_queue(1);
            bits = bfm.convert_message_to_bit_queue(data, bitLen);

            fd_validator.clear_expected_queue;
            fd_validator.push_soc_event;
            fd_validator.push_data_events(bits);
            fd_validator.push_eoc_event(1'b0);

            send_frame(bits);
        end

        // repeat these tests a bunch of times
        repeat (1000) begin
            // 1 - 1000 bits (range is a bit arbitrary, but should be good enough)
            automatic int       num_bits                = $urandom_range(1, 1000);
            automatic int       num_bytes               = int'($ceil(num_bits / 8.0));
            automatic int       num_bits_in_last_byte   = num_bits % 8;

            // 7) Test an N bit frame with parity OK
            //$display("Testing a %d bit frame with parity bits OK", num_bits);
            data = bfm.generate_byte_queue(num_bytes);
            bits = bfm.convert_message_to_bit_queue(data, num_bits_in_last_byte);

            fd_validator.clear_expected_queue;
            fd_validator.push_soc_event;
            fd_validator.push_data_events(bits);
            fd_validator.push_eoc_event(1'b0);

            bits = bfm.add_parity_to_bit_queue(bits);
            send_frame(bits);

            // 8) Test an N bit frame with parity FAIL
            if (num_bits > 8) begin
                automatic int broken_parity_byte    = $urandom_range(num_bytes - 2);
                //$display("Testing a %d bit frame with broken parity bit in byte %d", num_bits, broken_parity_byte);
                data = bfm.generate_byte_queue(num_bytes);

                bits = bfm.convert_message_to_bit_queue(data, num_bits_in_last_byte);

                fd_validator.clear_expected_queue;
                fd_validator.push_soc_event;
                fd_validator.push_data_events(bits[0:broken_parity_byte*8 + 7]);
                fd_validator.push_error_event;
                fd_validator.push_eoc_event(1'b0);

                bits = bfm.add_parity_to_bit_queue(bits);
                bits[broken_parity_byte*9 + 8] = !bits[broken_parity_byte*9 + 8]; // break the parity bit
                send_frame(bits);
            end

            // 9) Test an N byte frame with last parity missing
            num_bytes = $urandom_range(1, 100);
            //$display("Testing a %d byte frame with last parity missing", num_bytes);
            data = bfm.generate_byte_queue(num_bytes);
            bits = bfm.convert_message_to_bit_queue(data, 8);

            // expecting parity error on EOC
            fd_validator.clear_expected_queue;
            fd_validator.push_soc_event;
            fd_validator.push_data_events(bits);
            fd_validator.push_eoc_event(1'b1);

            bits = bfm.add_parity_to_bit_queue(bits);
            void'(bits.pop_back);   // remove the last bit

            send_frame(bits);
        end

        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

    // all the asserts are in frame_decode_validator

endmodule
