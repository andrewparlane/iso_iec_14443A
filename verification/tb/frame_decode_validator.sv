/***********************************************************************
        File: frame_decode_validator.sv
 Description: Validates outputs of the frame_decode module
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

module frame_decode_validator
(
    input       clk,
    input       rst_n,

    // frame_decode / rx outputs
    input       soc,
    input       eoc,
    input [7:0] data,
    input [2:0] data_bits,
    input       data_valid,
    input       sequence_error,
    input       parity_error
);

    // has something happened this tick?
    logic event_detected;
    assign event_detected = soc | eoc | sequence_error | parity_error | data_valid;

    // A struct to combine the frame_decode / rx outputs
    typedef struct
    {
        logic       soc;            // no other flags should be set
        logic       eoc;            // data_valid may be set if data_bits != 0
        logic       sequence_error; // no other flags should be set
        logic       parity_error;   // no other flags should be set
        logic       data_valid;     // eoc may be set if data_bits != 0;
        logic [2:0] data_bits;      // number of valid data bits
        logic [7:0] data;           // the data
    } FrameDecodeEvent;

    // helper type, so we can returne a FrameDecodeEvent queue from a function
    typedef FrameDecodeEvent FrameDecodeEventQueue [$];

    // What kind of error if any do we expect
    typedef enum
    {
        ErrorType_NONE,
        ErrorType_PARITY,
        ErrorType_SEQUENCE
    } ErrorType;

    // Check that the event is valid
    // this is used to make sure the outputs are always valid
    // and that any event we add to the "expected" queue is also valid
    function bit validate_event (FrameDecodeEvent e);
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

    // So we can print some debug info
    function automatic string event_to_string (FrameDecodeEvent e);
        automatic string res = "";
        $sformat(res, "soc %b, eoc %b, sequence_error %b, parity_error %b, data_valid %b, data_bits %d, data %b",
                 e.soc, e.eoc, e.sequence_error, e.parity_error,
                 e.data_valid, e.data_bits, e.data);
        return res;
    endfunction

    // ========================================================================
    // Some functions to construct events and add them to an expected queue
    // ========================================================================

    FrameDecodeEvent expected[$];

    function automatic void clear_expected_queue;
        expected.delete;
    endfunction

    function automatic bit expected_queue_is_empty;
        return expected.size == 0;
    endfunction

    // A function to build an event struct for the SOC event
    function automatic void push_soc_event;
        automatic FrameDecodeEvent e;
        e.soc               = 1;
        e.eoc               = 0;
        e.sequence_error    = 0;
        e.parity_error      = 0;
        e.data_valid        = 0;
        e.data_bits         = 0;
        e.data              = 8'hxx;

        expected.push_back(e);
    endfunction

    // A function to build an event struct for the EOC event
    // when the last byte is a full byte (standard frame), no data is issued
    // on the EOC event, there may however be an error.
    function automatic void push_eoc_full_byte_event (ErrorType err, bit check_data_bits=1);
        automatic FrameDecodeEvent e;
        e.soc               = 0;
        e.eoc               = 1;
        e.sequence_error    = (err == ErrorType_SEQUENCE);
        e.parity_error      = (err == ErrorType_PARITY);
        e.data_valid        = 0;
        e.data_bits         = check_data_bits ? 0 : 'x;
        e.data              = 8'hxx;

        expected.push_back(e);
    endfunction

    // A function to build an event struct for the EOC event
    // When the last byte is not a full byte (short frame / anticollision frame)
    // then the partial byte is issued on the EOC event
    function automatic void push_eoc_part_byte_event (int bitLen, bit [7:0] data);
        automatic FrameDecodeEvent  e;
        automatic logic [7:0]       new_data;

        // set the none used bits as x
        new_data = data;
        for (int i = 7; i >= bitLen; i--) begin
            new_data[i] = 1'bx;
        end

        e.soc             = 0;
        e.eoc             = 1;
        e.sequence_error  = 0;
        e.parity_error    = 0;
        e.data_valid      = 1;
        e.data_bits       = bitLen;
        e.data            = new_data;

        expected.push_back(e);
    endfunction

    // Add events for receiving a series of full bytes of data
    function automatic void push_data_events (bit [7:0] data[$]);

        foreach (data[i]) begin
            automatic FrameDecodeEvent e;
            e.soc               = 0;
            e.eoc               = 0;
            e.sequence_error    = 0;
            e.parity_error      = 0;
            e.data_valid        = 1;
            e.data_bits         = 0;
            e.data              = data[i];

            expected.push_back(e);
        end
    endfunction

    // Set up an event struct for an expected parity fail
    function automatic void push_parity_fail_event;
        automatic FrameDecodeEvent e;
        e.soc               = 0;
        e.eoc               = 0;
        e.sequence_error    = 0;
        e.parity_error      = 1;
        e.data_valid        = 0;
        e.data_bits         = 0;
        e.data              = 8'hxx;

        expected.push_back(e);
    endfunction

    // Set up an event struct for an expected sequenec error
    function automatic void push_sequence_error_event;
        automatic FrameDecodeEvent e;
        e.soc               = 0;
        e.eoc               = 0;
        e.sequence_error    = 1;
        e.parity_error      = 0;
        e.data_valid        = 0;
        e.data_bits         = 'hx;  // we don't know on which bit the error occured
        e.data              = 8'hxx;

        expected.push_back(e);
    endfunction

    // ========================================================================
    // Check that the current event (if any) is expected
    // ========================================================================

    // build a FrameDecodeEvent struct from the outputs
    FrameDecodeEvent outputs;
    always_comb begin
        outputs.soc               = soc;
        outputs.eoc               = eoc;
        outputs.sequence_error    = sequence_error;
        outputs.parity_error      = parity_error;
        outputs.data_valid        = data_valid;
        outputs.data_bits         = data_bits;
        outputs.data              = data;
    end

    always_ff @(posedge clk) begin
        if (event_detected) begin
            gotEventButNoneExpected:
                assert (expected.size != 0)
                else $error("event detected but not expecting anything");

            if (expected.size != 0) begin
                automatic FrameDecodeEvent expectedEvent = expected.pop_front;

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
    // Asserts
    // --------------------------------------------------------------

    // Check that the outputs are correct when in reset
    signalsInReset:
    assert property (
        @(posedge clk)
        !rst_n |->
            (!soc && !eoc &&
             !parity_error && !sequence_error &&
             !data_valid && !event_detected))
        else $error("Outputs not as expected whilst in reset");

    // Check that the outputs are always valid
    outputsValid:
    assert property (
        @(posedge clk)
        validate_event(outputs))
        else $error("Current outputs not valid");

    // soc is only valid for one tick at a time
    socOnlyOneTick:
    assert property (
        @(posedge clk)
        soc |=> !soc)
        else $error("soc asserted for more than one tick");

    // eoc is only valid for one tick at a time
    eocOnlyOneTick:
    assert property (
        @(posedge clk)
        eoc |=> !eoc)
        else $error("eoc asserted for more than one tick");

    // sequence_error is only valid for one tick at a time
    sequenceErrorOnlyOneTick:
    assert property (
        @(posedge clk)
        sequence_error |=> !sequence_error)
        else $error("sequence_error asserted for more than one tick");

    // parity_error is only valid for one tick at a time
    parityErrorOnlyOneTick:
    assert property (
        @(posedge clk)
        parity_error |=> !parity_error)
        else $error("parity_error asserted for more than one tick");

    // data_valid is only valid for one tick at a time
    dataValidOnlyOneTick:
    assert property (
        @(posedge clk)
        data_valid |=> !data_valid)
        else $error("data_valid asserted for more than one tick");

endmodule
