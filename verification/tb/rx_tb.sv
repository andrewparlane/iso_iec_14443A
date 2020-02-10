/***********************************************************************
        File: rx_tb.sv
 Description: Testbench for the rx module
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

module rx_tb;

    import ISO14443A_pkg::*;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic           clk;
    logic           rst_n;

    logic           pause_n_synchronised;

    logic           soc;
    logic           eoc;
    logic [7:0]     data;
    logic [2:0]     data_bits;
    logic           data_valid;
    logic           sequence_error;
    logic           parity_error;
    logic           last_bit;

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    rx dut (.*);

    // --------------------------------------------------------------
    // PICC -> PCD clock and comms generator
    // --------------------------------------------------------------
    logic bfm_sending;
    logic pause_n;
    iso14443a_pcd_to_picc_comms_generator bfm
    (
        .clk            (clk),
        .pcd_pause_n    (),             // not used
        .pause_n        (pause_n),
        .sending        (bfm_sending)
    );

    // --------------------------------------------------------------
    // Synchronise the pause_n signal
    // --------------------------------------------------------------
    // this is done in the top level module and passed to the rx component
    // for synthesis
    active_low_reset_synchroniser pause_n_synchroniser
    (
        .clk        (clk),
        .rst_n_in   (pause_n),
        .rst_n_out  (pause_n_synchronised)
    );

    // --------------------------------------------------------------
    // Verify results are as expected
    // --------------------------------------------------------------

    frame_decode_validator fd_validator (.*);

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    typedef enum
    {
        TestType_DATA_OK,
        TestType_PARITY_FAIL,
        TestType_PARITY_MISSING,
        TestType_SEQUENCE_ERROR
    } TestType;

    initial begin: testStimulus
        automatic bit [7:0]         data[$];
        automatic bit               bits[$];
        automatic PCDBitSequence    seqs[$];
        automatic logic expected_queue_empty;

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // 1) Test a single pause blip (0 byte frame: ZYY)
        // note we add the extra Y so that the EOC is detected
        // this is fine, since sequence_decode only goes idle after two Ys
        // We do this here, because this case never gets generated in the
        // random transfers below. A 0 byte frame there, generates ZZY.
        //$display("Testing a 0 bit frame (ZYY) (sequence error)");
        fd_validator.clear_expected_queue;
        fd_validator.push_soc_event;
        fd_validator.push_eoc_full_byte_event(fd_validator.ErrorType_SEQUENCE);

        seqs = '{PCDBitSequence_Z,
                 PCDBitSequence_Y,
                 PCDBitSequence_Y};
        bfm.send_sequence_queue(seqs);

        expected_queue_empty = fd_validator.expected_queue_is_empty();
        expectedQueueEmpty1: assert(expected_queue_empty) else $fatal(1, "Finished transmitting but expected queue is not empty");

        // TODO: Increase test count to lots
        //       should also do this in all TBs
        //       Do this once switched to synopsys VCS

        // Test random Transfers
        repeat (1000) begin: randomTransferLoop
            // first, how many bits to send? Max 80 bits = 10 bytes, Min 0 bits
            automatic int bits_to_send          = $urandom_range(80);
            automatic int bytes_to_send         = int'($ceil(bits_to_send / 8.0));
            automatic int bits_in_last_byte     = bits_to_send % 8;

            if (bits_to_send == 0) begin
                //$display("Testing a 0 bit frame (ZZY) (sequence error)");

                // sequence error
                fd_validator.clear_expected_queue;
                fd_validator.push_soc_event;
                fd_validator.push_eoc_full_byte_event(fd_validator.ErrorType_SEQUENCE);

                bits.delete;
                bfm.send_bit_queue_no_parity(bits);
            end
            else begin
                // what test do we run?
                automatic TestType test = TestType'($urandom_range(test.num - 1));

                // generate the data
                data = bfm.generate_byte_queue(bytes_to_send);

                // start the expected queue with the SOC event
                fd_validator.clear_expected_queue;
                fd_validator.push_soc_event;

                case (test)
                    TestType_DATA_OK: begin
                        //$display("Testing a valid %d bit frame", bits_to_send);
                        // add the data and EOC
                        if (bits_in_last_byte == 0) begin
                            // send whole number of bytes, so push everything
                            fd_validator.push_data_events(data[0:$]);
                            // add the EOC event
                            fd_validator.push_eoc_full_byte_event(fd_validator.ErrorType_NONE);
                        end
                        else begin
                            if (bytes_to_send != 1) begin
                                // push all but the last byte
                                fd_validator.push_data_events(data[0:$-1]);
                            end
                            // then add the last partial byte + EOC
                            fd_validator.push_eoc_part_byte_event(bits_in_last_byte, data[$]);
                        end

                        bfm.send_message_no_crc(data, bits_in_last_byte);
                    end

                    TestType_PARITY_FAIL: begin
                        automatic int parity_error_in_byte;

                        if (bits_in_last_byte == 0) begin
                            // parity error can be in any byte
                            parity_error_in_byte = $urandom_range(bytes_to_send - 1);
                        end
                        else begin
                            if (bytes_to_send == 1) begin
                                // to have a parity fail we need to send at least one full bytes
                                bytes_to_send++;
                                bits_to_send = bits_to_send + 8;

                                // and regenerate the message
                                data = bfm.generate_byte_queue(bytes_to_send);
                            end

                            // parity error can't be in the last byte
                            parity_error_in_byte = $urandom_range(bytes_to_send - 2);
                        end

                        //$display("Testing a %d bit frame with parity error in byte %d", bits_to_send, parity_error_in_byte);

                        // Add all the valid data bytes
                        if (parity_error_in_byte != 0) begin
                            fd_validator.push_data_events(data[0:parity_error_in_byte-1]);
                        end

                        // add the parity eror
                        fd_validator.push_parity_fail_event;

                        // add the EOC
                        fd_validator.push_eoc_full_byte_event(fd_validator.ErrorType_NONE);

                        // get the bit queue with the correct parity bits
                        bits = bfm.convert_message_to_bit_queue(data, bits_in_last_byte);
                        bits = bfm.add_parity_to_bit_queue(bits);

                        // flip the parity bit in the relevant byte
                        bits[parity_error_in_byte*9 + 8] = !bits[parity_error_in_byte*9 + 8];

                        // send it
                        bfm.send_bit_queue_no_parity(bits);
                    end

                    TestType_PARITY_MISSING: begin
                        // for parity missing, we need to have a whole number of bytes
                        bits_in_last_byte = 0;

                        //$display("Testing a %d bit frame with missing parity on last byte", bytes_to_send*8);

                        // get the bit queue with the correct parity bits
                        bits = bfm.convert_message_to_bit_queue(data, bits_in_last_byte);
                        bits = bfm.add_parity_to_bit_queue(bits);

                        // drop the last bit (final parity)
                        void'(bits.pop_back);

                        // add all the data expcept the last byte
                        if (bytes_to_send != 1) begin
                            fd_validator.push_data_events(data[0:$-1]);
                        end

                        // parity error on EOC
                        fd_validator.push_eoc_full_byte_event(fd_validator.ErrorType_PARITY);

                        // send it
                        bfm.send_bit_queue_no_parity(bits);
                    end

                    TestType_SEQUENCE_ERROR: begin
                        automatic int num_xs;
                        automatic int x_to_change;
                        automatic int seq_changed;
                        automatic int err_byte_idx;

                        // get our sequence queue
                        bits = bfm.convert_message_to_bit_queue(data, bits_in_last_byte);
                        bits = bfm.add_parity_to_bit_queue(bits);
                        seqs = bfm.convert_bit_queue_to_sequence_queue(bits);

                        // sequence_decode generates a PCDBitSequence_ERROR if two pauses are
                        // too close together. The easiest way to do this is X -> Z
                        // if we could use std::randomize() with {}...

                        // we could pick an index i, such that the previous seq was an X and
                        // change seqs[i] to be a Z. But we can't use constrained random
                        // since I don't have the license.
                        // so instead we count the number of Xs in the sequence queue
                        // pick one randomly and change the next value to a Z

                        // count Xs in the sequence queue
                        num_xs = 0;
                        foreach (seqs[i]) begin
                            if (seqs[i] == PCDBitSequence_X) begin
                                num_xs++;
                            end
                        end

                        if (num_xs == 0) begin
                            // could insert an X before a Z
                            // but there's not much point,
                            // just abort this test
                            continue;
                        end

                        x_to_change = $urandom_range(num_xs - 1);

                        // find that X again
                        num_xs = 0;
                        seq_changed = 0;
                        foreach (seqs[i]) begin
                            if (seqs[i] == PCDBitSequence_X) begin
                                if (x_to_change == num_xs) begin
                                    // This is our X, change the next seq to a Z
                                    seqs[i+1] = PCDBitSequence_Z;
                                    seq_changed = i+1;
                                    break;
                                end
                                num_xs++;
                            end
                        end

                        // figure out in which byte we introduced the error
                        // -1 for the SOC, /9 for 9 bits per byte (8 + parity)
                        err_byte_idx = (seq_changed - 1) / 9;

                        //$display("Testing a %d bit frame with sequence error idx %d", bits_to_send, seq_changed);

                        if (err_byte_idx != 0) begin
                            // push valid bytes
                            fd_validator.push_data_events(data[0:err_byte_idx-1]);
                        end

                        // push sequence_error
                        fd_validator.push_sequence_error_event;

                        // push EOC
                        fd_validator.push_eoc_full_byte_event(fd_validator.ErrorType_NONE, 0);

                        // send it
                        bfm.send_sequence_queue(seqs);
                    end
                endcase
            end

            expected_queue_empty = fd_validator.expected_queue_is_empty();
            expectedQueueEmpty2: assert(expected_queue_empty) else $fatal(1, "Finished transmitting but expected queue is not empty");

        end

        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

    // all the asserts are in frame_decode_validator

endmodule
