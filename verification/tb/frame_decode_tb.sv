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

    PCDBitSequence  sd_seq;
    logic           sd_seq_valid;

    logic           soc;
    logic           eoc;
    logic [7:0]     data;
    logic [2:0]     data_bits;
    logic           data_valid;
    logic           sequence_error;
    logic           parity_error;

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
        .clk     (clk),
        .pause_n (),
        .sending ()
    );

    // --------------------------------------------------------------
    // Verify results are as expected
    // --------------------------------------------------------------

    frame_decode_validator fd_validator (.*);

    // --------------------------------------------------------------
    // Task to send sequence queues
    // --------------------------------------------------------------

    task send_sequence_queue (PCDBitSequence seqs[$]);
        foreach (seqs[i]) begin
            repeat (5) @(posedge clk) begin end // sync to clock edge and delay between seqs

            sd_seq          = seqs[i];
            sd_seq_valid    = 1;
            @(posedge clk) begin end
            sd_seq_valid    = 0;
        end

        repeat (5) @(posedge clk) begin end
        assert (fd_validator.expected_queue_is_empty) else $error("Finished sending but still expected data");
    endtask


    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin
        automatic bit [7:0]         data[$];
        automatic bit               bits[$];
        automatic PCDBitSequence    seqs[$];

        sd_seq_valid = 0;

        // reset for 5 ticks
        rst_n <= 0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1;
        repeat (5) @(posedge clk) begin end

        // 1) Test an 8 bit frame with parity bit OK
        //$display("Testing an 8 bit frame with parity bit OK");
        data = bfm.generate_byte_queue(1);
        fd_validator.clear_expected_queue;
        fd_validator.push_soc_event;
        fd_validator.push_data_events(data);
        fd_validator.push_eoc_full_byte_event(fd_validator.ErrorType_NONE);

        bits = bfm.convert_message_to_bit_queue(data, 8);
        bits = bfm.add_parity_to_bit_queue(bits);
        seqs = bfm.convert_bit_queue_to_sequence_queue(bits);

        send_sequence_queue(seqs);

        // 2) Test an 8 bit frame with parity FAIL
        //$display("Testing an 8 bit frame with parity FAIL");
        data = bfm.generate_byte_queue(1);
        fd_validator.clear_expected_queue;
        fd_validator.push_soc_event;
        fd_validator.push_parity_fail_event;
        fd_validator.push_eoc_full_byte_event(fd_validator.ErrorType_NONE);

        bits = bfm.convert_message_to_bit_queue(data, 8);
        bits = bfm.add_parity_to_bit_queue(bits);
        bits[$] = !bits[$]; // flip the parity bit
        seqs = bfm.convert_bit_queue_to_sequence_queue(bits);

        send_sequence_queue(seqs);

        // 3) Test an 8 bit frame with parity missing
        //$display("Testing an 8 bit frame with parity bit missing");
        data = bfm.generate_byte_queue(1);
        fd_validator.clear_expected_queue;
        fd_validator.push_soc_event;
        fd_validator.push_eoc_full_byte_event(fd_validator.ErrorType_PARITY);

        bits = bfm.convert_message_to_bit_queue(data, 8);
        // don't add parity bit
        seqs = bfm.convert_bit_queue_to_sequence_queue(bits);

        send_sequence_queue(seqs);

        // 4) Test an 8 bit frame with sequence error in one location
        // don't mess with SOC (idx 0) or EOC (idx 10, 11)
        for (int i = 1; i <= 9; i++) begin
            //$display("Testing an 8 bit frame with a sequence error at idx %d", i);
            data = bfm.generate_byte_queue(1);
            fd_validator.clear_expected_queue;
            fd_validator.push_soc_event;
            fd_validator.push_sequence_error_event;
            fd_validator.push_eoc_full_byte_event(fd_validator.ErrorType_NONE, 0);

            bits = bfm.convert_message_to_bit_queue(data, 8);
            bits = bfm.add_parity_to_bit_queue(bits);
            seqs = bfm.convert_bit_queue_to_sequence_queue(bits);
            seqs[i] = PCDBitSequence_ERROR;

            send_sequence_queue(seqs);
        end

        // 5a) Test a 0 bit frame (ZYY) (sequence error)
        // note we add the extra Y so that the EOC is detected
        // this is fine, since sequence_decode only goes idle after two Ys
        //$display("Testing a 0 bit frame (ZYY) (sequence error)");
        fd_validator.clear_expected_queue;
        fd_validator.push_soc_event;
        fd_validator.push_eoc_full_byte_event(fd_validator.ErrorType_SEQUENCE);

        seqs = '{PCDBitSequence_Z,
                 PCDBitSequence_Y,
                 PCDBitSequence_Y};
        send_sequence_queue(seqs);

        // 5b) Test a 0 bit frame (ZZY) (sequence error)
        //$display("Testing a 0 bit frame (ZZY) (sequence error)");
        fd_validator.clear_expected_queue;
        fd_validator.push_soc_event;
        fd_validator.push_eoc_full_byte_event(fd_validator.ErrorType_SEQUENCE);

        seqs = '{PCDBitSequence_Z,
                 PCDBitSequence_Z,
                 PCDBitSequence_Y};
        send_sequence_queue(seqs);

        // 6) test 1 - 7 bit frames
        for (int bitLen = 1; bitLen <= 7; bitLen++) begin
            //$display("Testing a %d bit frame", bitLen);
            data = bfm.generate_byte_queue(1);
            fd_validator.clear_expected_queue;

            data = bfm.generate_byte_queue(1);
            fd_validator.clear_expected_queue;
            fd_validator.push_soc_event;
            fd_validator.push_eoc_part_byte_event(bitLen, data[0]);

            bits = bfm.convert_message_to_bit_queue(data, bitLen);
            seqs = bfm.convert_bit_queue_to_sequence_queue(bits);

            send_sequence_queue(seqs);
        end

        // repeat these tests a bunch of times
        repeat (1000) begin
            // 1 - 1000 bits (range is a bit arbitrary, but should be good enough)
            automatic int num_bits              = $urandom_range(1, 1000);
            automatic int num_bytes             = $ceil(num_bits / 8.0);
            automatic int num_bits_in_last_byte = num_bits % 8;
            automatic int last_byte;

            // 7) Test an N bit frame with parity OK
            //$display("Testing a %d bit frame with parity bits OK", num_bits);
            data = bfm.generate_byte_queue(num_bytes);

            bits = bfm.convert_message_to_bit_queue(data, num_bits_in_last_byte);
            bits = bfm.add_parity_to_bit_queue(bits);
            seqs = bfm.convert_bit_queue_to_sequence_queue(bits);

            if (num_bits_in_last_byte != 0) begin
                last_byte = data.pop_back;
            end

            fd_validator.clear_expected_queue;
            fd_validator.push_soc_event;
            fd_validator.push_data_events(data);
            if (num_bits_in_last_byte == 0) begin
                fd_validator.push_eoc_full_byte_event(fd_validator.ErrorType_NONE);
            end
            else begin
                fd_validator.push_eoc_part_byte_event(num_bits_in_last_byte, last_byte);
            end

            send_sequence_queue(seqs);

            // 8) Test an N bit frame with parity FAIL
            if (num_bits > 8) begin
                automatic int broken_parity_byte    = $urandom_range(num_bytes - 2);
                //$display("Testing a %d bit frame with broken parity bit in byte %d", num_bits, broken_parity_byte);
                data = bfm.generate_byte_queue(num_bytes);

                bits = bfm.convert_message_to_bit_queue(data, num_bits_in_last_byte);
                bits = bfm.add_parity_to_bit_queue(bits);
                bits[broken_parity_byte*9 + 8] = !bits[broken_parity_byte*9 + 8]; // break the parity bit
                seqs = bfm.convert_bit_queue_to_sequence_queue(bits);

                if (num_bits_in_last_byte != 0) begin
                    last_byte = data.pop_back;
                end

                fd_validator.clear_expected_queue;
                fd_validator.push_soc_event;
                if (broken_parity_byte != 0) begin
                    fd_validator.push_data_events(data[0:broken_parity_byte-1]);
                end
                fd_validator.push_parity_fail_event;
                fd_validator.push_eoc_full_byte_event(fd_validator.ErrorType_NONE);

                send_sequence_queue(seqs);
            end

            // 9) Test an N byte frame with last parity missing
            num_bytes = $urandom_range(1, 100);
            //$display("Testing a %d byte frame with last parity missing", num_bytes);
            data = bfm.generate_byte_queue(num_bytes);

            bits = bfm.convert_message_to_bit_queue(data, 8);
            bits = bfm.add_parity_to_bit_queue(bits);
            void'(bits.pop_back);   // remove the last bit
            seqs = bfm.convert_bit_queue_to_sequence_queue(bits);

            // expecting parity error in last byte, so remove it
            void'(data.pop_back);
            fd_validator.clear_expected_queue;
            fd_validator.push_soc_event;
            fd_validator.push_data_events(data);
            fd_validator.push_eoc_full_byte_event(fd_validator.ErrorType_PARITY);

            send_sequence_queue(seqs);
        end

        // 10) Confirm data is received LSb first
        //$display("Testing LSb first");
        fd_validator.clear_expected_queue;
        fd_validator.push_soc_event;
        fd_validator.push_data_events('{8'h29});
        fd_validator.push_eoc_full_byte_event(fd_validator.ErrorType_NONE);

        // 8'h29 = 8'b00101001
        // LSb first: 10010100 + parity 0

        seqs = '{PCDBitSequence_Z,  // SOC
                 PCDBitSequence_X,  // 1
                 PCDBitSequence_Y,  // 0
                 PCDBitSequence_Z,  // 0
                 PCDBitSequence_X,  // 1
                 PCDBitSequence_Y,  // 0
                 PCDBitSequence_X,  // 1
                 PCDBitSequence_Y,  // 0
                 PCDBitSequence_Z,  // 0
                 PCDBitSequence_Z,  // 0 (parity)
                 PCDBitSequence_Z,  // EOC
                 PCDBitSequence_Y}; // EOC

        send_sequence_queue(seqs);

        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

    // all the asserts are in frame_decode_validator

endmodule
