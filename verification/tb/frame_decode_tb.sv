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

import ISO14443A_pkg::*;

module frame_decode_tb;
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
    // Task to send sequence queues
    // --------------------------------------------------------------

    task send_sequence_queue (PCDBitSequence seqs[$]);
        foreach (seqs[i]) begin
            repeat (5) @(posedge clk);  // sync to clock edge and delay between seqs

            sd_seq          = seqs[i];
            sd_seq_valid    = 1;
            @(posedge clk);
            sd_seq_valid    = 0;
        end

        repeat (5) @(posedge clk);
        assert (expected.size == 0) else $error("Finished sending but still expected data");
    endtask

    // --------------------------------------------------------------
    // Verify bytes are as expected
    // --------------------------------------------------------------

    typedef struct
    {
        logic       soc;            // no other flags should be set
        logic       eoc;            // data_valid may be set if data_bits != 0
        logic       sequence_error; // no other flags should be set
        logic       parity_error;   // no other flags should be set
        logic       data_valid;     // eoc may be set if data_bits != 0;
        logic [2:0] data_bits;      // number of valid data bits
        logic [7:0] data;           // the data
    } FrameDecodeOutput;

    typedef enum
    {
        ErrorType_NONE,
        ErrorType_PARITY,
        ErrorType_SEQUENCE
    } ErrorType;

    function bit validate_event (FrameDecodeOutput e);
        automatic bit err = 0;

        if (e.soc) begin
            // eoc, sequence_error, parity_error, data_valid must not be set
            // data_bits must be 0
            if (e.eoc || e.sequence_error || e.parity_error || e.data_valid || e.data_bits != 0) begin
                err = 1;
            end
        end

        if (e.eoc) begin
            // soc must not be set
            // data_valid can only be set if data_bits != 0
            if (e.soc) begin
                err = 1;
            end
            if (e.data_valid && (e.data_bits == 0)) begin
                err = 1;
            end
        end

        if (e.sequence_error) begin
            // soc, parity_error, data_valid must not be set
            // data_bits must be 0
            if (e.soc || e.parity_error || e.data_valid) begin
                err = 1;
            end
        end

        if (e.parity_error) begin
            // soc, sequence_error, data_valid must not be set
            // data_bits must be 0
            if (e.soc || e.sequence_error || e.data_valid) begin
                err = 1;
            end
        end

        if (e.data_valid) begin
            // none of soc, sequence_error or parity_error may be set
            if (e.soc || e.sequence_error || e.parity_error) begin
                err = 1;
            end

            // data bits must be none 0 if EOC is set
            if (e.eoc && (e.data_bits == 0)) begin
                err = 1;
            end

            // otherwise data bits must be 0
            if (!e.eoc && e.data_bits != 0) begin
                err = 1;
            end
        end

        return !err;
    endfunction

    function automatic string event_to_string (FrameDecodeOutput e);
        automatic string res = "";
        $sformat(res, "soc %b, eoc %b, sequence_error %b, parity_error %b, data_valid %b, data_bits %d, data %b",
                 e.soc, e.eoc, e.sequence_error, e.parity_error,
                 e.data_valid, e.data_bits, e.data);
        return res;
    endfunction

    function automatic FrameDecodeOutput construct_soc_event;
        automatic FrameDecodeOutput res;
        res.soc             = 1;
        res.eoc             = 0;
        res.sequence_error  = 0;
        res.parity_error    = 0;
        res.data_valid      = 0;
        res.data_bits       = 0;
        res.data            = 8'hxx;
        return res;
    endfunction

    function automatic FrameDecodeOutput construct_eoc_full_byte_event (ErrorType err, bit check_data_bits=1);
        automatic FrameDecodeOutput res;
        res.soc             = 0;
        res.eoc             = 1;
        res.sequence_error  = (err == ErrorType_SEQUENCE);
        res.parity_error    = (err == ErrorType_PARITY);
        res.data_valid      = 0;
        res.data_bits       = check_data_bits ? 0 : 'x;
        res.data            = 8'hxx;
        return res;
    endfunction

    function automatic FrameDecodeOutput construct_eoc_part_byte_event (int bitLen, bit [7:0] data);
        automatic FrameDecodeOutput res;
        automatic logic [7:0]       new_data;

        // set the none used bits as x
        new_data = data;
        for (int i = 7; i >= bitLen; i--) begin
            new_data[i] = 1'bx;
        end

        res.soc             = 0;
        res.eoc             = 1;
        res.sequence_error  = 0;
        res.parity_error    = 0;
        res.data_valid      = 1;
        res.data_bits       = bitLen;
        res.data            = new_data;
        return res;
    endfunction

    typedef FrameDecodeOutput FrameDecodeOutputQueue [$];
    function automatic FrameDecodeOutputQueue construct_data_events (bit [7:0] data[$]);
        automatic FrameDecodeOutputQueue res;

        foreach (data[i]) begin
            automatic FrameDecodeOutput e;
            e.soc               = 0;
            e.eoc               = 0;
            e.sequence_error    = 0;
            e.parity_error      = 0;
            e.data_valid        = 1;
            e.data_bits         = 0;
            e.data              = data[i];
            res.push_back(e);
        end
        return res;
    endfunction

    function automatic FrameDecodeOutput construct_parity_fail_event;
        automatic FrameDecodeOutput res;
        res.soc             = 0;
        res.eoc             = 0;
        res.sequence_error  = 0;
        res.parity_error    = 1;
        res.data_valid      = 0;
        res.data_bits       = 0;
        res.data            = 8'hxx;
        return res;
    endfunction

    function automatic FrameDecodeOutput construct_sequence_error_event;
        automatic FrameDecodeOutput res;
        res.soc             = 0;
        res.eoc             = 0;
        res.sequence_error  = 1;
        res.parity_error    = 0;
        res.data_valid      = 0;
        res.data_bits       = 'hx;  // we don't know on which bit the error occured
        res.data            = 8'hxx;
        return res;
    endfunction

    logic event_detected;
    assign event_detected = soc | eoc | sequence_error | parity_error | data_valid;

    // build a FrameDecodeOutput struct from the outputs
    FrameDecodeOutput outputs;
    always_comb begin
        outputs.soc               = soc;
        outputs.eoc               = eoc;
        outputs.sequence_error    = sequence_error;
        outputs.parity_error      = parity_error;
        outputs.data_valid        = data_valid;
        outputs.data_bits         = data_bits;
        outputs.data              = data;
    end

    FrameDecodeOutput expected[$];

    always_ff @(posedge clk) begin
        if (event_detected) begin
            gotEventButNoneExpected:
                assert (expected.size != 0)
                else $error("event detected but not expecting anything");

            if (expected.size != 0) begin
                automatic FrameDecodeOutput expectedEvent = expected.pop_front;

                expectedEventValid:
                    assert (validate_event(expectedEvent))
                    else $fatal(1, "An expected event was found not valid");

                eventNotAsExpected:
                    assert (outputs ==? expectedEvent)  // ==? so we allow 'x in expectedEvent as a wildcard
                    else $error("Detected event is not as expected. Got %s, expected %s",
                                event_to_string(outputs), event_to_string(expectedEvent));
            end
        end
    end

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
        repeat (5) @(posedge clk);
        rst_n <= 1;
        repeat (5) @(posedge clk);

        // 1) Test an 8 bit frame with parity bit OK
        $display("Testing an 8 bit frame with parity bit OK");
        data = bfm.generate_byte_queue(1);
        expected.delete;
        expected.push_back(construct_soc_event);
        expected = {expected, construct_data_events(data)};
        expected.push_back(construct_eoc_full_byte_event(ErrorType_NONE));

        bits = bfm.convert_message_to_bit_queue(data, 8);
        bits = bfm.add_parity_to_bit_queue(bits);
        seqs = bfm.convert_bit_queue_to_sequence_queue(bits);

        send_sequence_queue(seqs);

        // 2) Test an 8 bit frame with parity FAIL
        $display("Testing an 8 bit frame with parity FAIL");
        data = bfm.generate_byte_queue(1);
        expected.delete;
        expected.push_back(construct_soc_event);
        expected.push_back(construct_parity_fail_event);
        expected.push_back(construct_eoc_full_byte_event(ErrorType_NONE));

        bits = bfm.convert_message_to_bit_queue(data, 8);
        bits = bfm.add_parity_to_bit_queue(bits);
        bits[$] = !bits[$]; // flip the parity bit
        seqs = bfm.convert_bit_queue_to_sequence_queue(bits);

        send_sequence_queue(seqs);

        // 3) Test an 8 bit frame with parity missing
        $display("Testing an 8 bit frame with parity bit missing");
        data = bfm.generate_byte_queue(1);
        expected.delete;
        expected.push_back(construct_soc_event);
        expected.push_back(construct_eoc_full_byte_event(ErrorType_PARITY));

        bits = bfm.convert_message_to_bit_queue(data, 8);
        // don't add parity bit
        seqs = bfm.convert_bit_queue_to_sequence_queue(bits);

        send_sequence_queue(seqs);

        // 4) Test an 8 bit frame with sequence error in one location
        // don't mess with SOC (idx 0) or EOC (idx 10, 11)
        for (int i = 1; i <= 9; i++) begin
            $display("Testing an 8 bit frame with a sequence error at idx %d", i);
            data = bfm.generate_byte_queue(1);
            expected.delete;
            expected.push_back(construct_soc_event);
            expected.push_back(construct_sequence_error_event);
            expected.push_back(construct_eoc_full_byte_event(ErrorType_NONE, 0));

            bits = bfm.convert_message_to_bit_queue(data, 8);
            bits = bfm.add_parity_to_bit_queue(bits);
            seqs = bfm.convert_bit_queue_to_sequence_queue(bits);
            seqs[i] = PCDBitSequence_ERROR;

            send_sequence_queue(seqs);
        end

        // 5a) Test a 0 bit frame (ZYY) (sequence error)
        // note we add the extra Y so that the EOC is detected
        // this is fine, since sequence_decode only goes idle after two Ys
        $display("Testing a 0 bit frame (ZYY) (sequence error)");
        expected.delete;
        expected.push_back(construct_soc_event);
        expected.push_back(construct_eoc_full_byte_event(ErrorType_SEQUENCE));

        seqs = '{PCDBitSequence_Z,
                 PCDBitSequence_Y,
                 PCDBitSequence_Y};
        send_sequence_queue(seqs);

        // 5b) Test a 0 bit frame (ZZY) (sequence error)
        $display("Testing a 0 bit frame (ZZY) (sequence error)");
        expected.delete;
        expected.push_back(construct_soc_event);
        expected.push_back(construct_eoc_full_byte_event(ErrorType_SEQUENCE));

        seqs = '{PCDBitSequence_Z,
                 PCDBitSequence_Z,
                 PCDBitSequence_Y};
        send_sequence_queue(seqs);

        // 6) test 1 - 7 bit frames
        for (int bitLen = 1; bitLen <= 7; bitLen++) begin
            $display("Testing a %d bit frame", bitLen);
            data = bfm.generate_byte_queue(1);
            expected.delete;

            data = bfm.generate_byte_queue(1);
            expected.delete;
            expected.push_back(construct_soc_event);
            expected.push_back(construct_eoc_part_byte_event(bitLen, data[0]));

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
            $display("Testing a %d bit frame with parity bits OK", num_bits);
            data = bfm.generate_byte_queue(num_bytes);

            bits = bfm.convert_message_to_bit_queue(data, num_bits_in_last_byte);
            bits = bfm.add_parity_to_bit_queue(bits);
            seqs = bfm.convert_bit_queue_to_sequence_queue(bits);

            if (num_bits_in_last_byte != 0) begin
                last_byte = data.pop_back;
            end

            expected.delete;
            expected.push_back(construct_soc_event);
            expected = {expected, construct_data_events(data)};
            if (num_bits_in_last_byte == 0) begin
                expected.push_back(construct_eoc_full_byte_event(ErrorType_NONE));
            end
            else begin
                expected.push_back(construct_eoc_part_byte_event(num_bits_in_last_byte, last_byte));
            end

            send_sequence_queue(seqs);

            // 8) Test an N bit frame with parity FAIL
            if (num_bits > 8) begin
                automatic int broken_parity_byte    = $urandom_range(num_bytes - 2);
                $display("Testing a %d bit frame with broken parity bit in byte %d", num_bits, broken_parity_byte);
                data = bfm.generate_byte_queue(num_bytes);

                bits = bfm.convert_message_to_bit_queue(data, num_bits_in_last_byte);
                bits = bfm.add_parity_to_bit_queue(bits);
                bits[broken_parity_byte*9 + 8] = !bits[broken_parity_byte*9 + 8]; // break the parity bit
                seqs = bfm.convert_bit_queue_to_sequence_queue(bits);

                if (num_bits_in_last_byte != 0) begin
                    last_byte = data.pop_back;
                end

                expected.delete;
                expected.push_back(construct_soc_event);
                if (broken_parity_byte != 0) begin
                    expected = {expected, construct_data_events(data[0:broken_parity_byte-1])};
                end
                expected.push_back(construct_parity_fail_event);
                expected.push_back(construct_eoc_full_byte_event(ErrorType_NONE));

                send_sequence_queue(seqs);
            end

            // 9) Test an N byte frame with last parity missing
            num_bytes = $urandom_range(1, 100);
            $display("Testing a %d byte frame with last parity missing", num_bytes);
            data = bfm.generate_byte_queue(num_bytes);

            bits = bfm.convert_message_to_bit_queue(data, 8);
            bits = bfm.add_parity_to_bit_queue(bits);
            void'(bits.pop_back);   // remove the last bit
            seqs = bfm.convert_bit_queue_to_sequence_queue(bits);

            // expecting parity error in last byte, so remove it
            void'(data.pop_back);
            expected.delete;
            expected.push_back(construct_soc_event);
            expected = {expected, construct_data_events(data)};
            expected.push_back(construct_eoc_full_byte_event(ErrorType_PARITY));

            send_sequence_queue(seqs);
        end

        // 10) Confirm data is received LSb first
        $display("Testing LSb first");
        expected.delete;
        expected.push_back(construct_soc_event);
        expected = {expected, construct_data_events('{8'h29})};
        expected.push_back(construct_eoc_full_byte_event(ErrorType_NONE));

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

        repeat (5) @(posedge clk);
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

    // Check that the outputs are correct when in reset
    signalsInReset:
    assert property (
        @(posedge clk)
        !rst_n |->
            (!soc && !eoc &&
             !parity_error && !sequence_error &&
             !data_valid && !event_detected));

    // Check that the outputs are always valid
    outputsValid:
    assert property (
        @(posedge clk)
        validate_event(outputs));

    // soc is only valid for one tick at a time
    socOnlyOneTick:
    assert property (
        @(posedge clk)
        soc |=> !soc);

    // eoc is only valid for one tick at a time
    eocOnlyOneTick:
    assert property (
        @(posedge clk)
        eoc |=> !eoc);

    // sequence_error is only valid for one tick at a time
    sequenceErrorOnlyOneTick:
    assert property (
        @(posedge clk)
        sequence_error |=> !sequence_error);

    // parity_error is only valid for one tick at a time
    parityErrorOnlyOneTick:
    assert property (
        @(posedge clk)
        parity_error |=> !parity_error);

    // data_valid is only valid for one tick at a time
    dataValidOnlyOneTick:
    assert property (
        @(posedge clk)
        data_valid |=> !data_valid);

endmodule
