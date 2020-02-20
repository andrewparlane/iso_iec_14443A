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
    input       data,
    input       data_valid,
    input       error,

    // we only care about this after the frame is done, so we don't add it to the
    // FrameDecodeEvent struct
    input       last_bit
);

    // has something happened this tick?
    logic event_detected;
    assign event_detected = soc | eoc | error | data_valid;

    // A struct to combine the frame_decode / rx outputs
    typedef struct packed
    {
        logic soc;          // no other flags should be set
        logic eoc;          // error can be set, but no others
        logic error;        // eoc can be set, but no others
        logic data_valid;   // no other flags should be set
        logic data;         // the data
    } FrameDecodeEvent;

    localparam FrameDecodeEvent EVENT_SOC       = '{1'b1, 1'b0, 1'b0, 1'b0, 1'bx};
    localparam FrameDecodeEvent EVENT_EOC       = '{1'b0, 1'b1, 1'b0, 1'b0, 1'bx};
    localparam FrameDecodeEvent EVENT_EOC_ERR   = '{1'b0, 1'b1, 1'b1, 1'b0, 1'bx};
    localparam FrameDecodeEvent EVENT_ERROR     = '{1'b0, 1'b0, 1'b1, 1'b0, 1'bx};
    localparam FrameDecodeEvent EVENT_DATA_0    = '{1'b0, 1'b0, 1'b0, 1'b1, 1'b0};
    localparam FrameDecodeEvent EVENT_DATA_1    = '{1'b0, 1'b0, 1'b0, 1'b1, 1'b1};

    // helper type, so we can returne a FrameDecodeEvent queue from a function
    typedef FrameDecodeEvent FrameDecodeEventQueue [$];

    // Check that the event is valid
    // this is used to make sure the outputs are always valid
    // and that any event we add to the "expected" queue is also valid
    function bit validate_event (FrameDecodeEvent e);
        automatic bit err = 1'b0;

        if (e.soc) begin
            // no other flags can be set
            if (e.eoc || e.error || e.data_valid) begin
                err = 1'b1;
            end
        end

        if (e.eoc) begin
            // only error can be set
            if (e.soc || e.data_valid) begin
                err = 1'b1;
            end
        end

        if (e.error) begin
            // only eoc can be set
            if (e.soc || e.data_valid) begin
                err = 1'b1;
            end
        end

        if (e.data_valid) begin
            // none of the other flags can be set
            if (e.soc || e.eoc || e.error) begin
                err = 1'b1;
            end
        end

        return !err;
    endfunction


    // ========================================================================
    // Some functions to construct events and add them to an expected queue
    // ========================================================================

    FrameDecodeEvent    expected[$];
    logic               expectedLastBit;

    function automatic void clear_expected_queue;
        expected.delete;
    endfunction

    function automatic bit expected_queue_is_empty;
        return expected.size == 0;
    endfunction

    // A function to build an event struct for the SOC event
    function automatic void push_soc_event;
        expected.push_back(EVENT_SOC);
        expectedLastBit = 1'bx; // start off with not checking the lastBit, unless we add data
    endfunction

    // A function to build an event struct for the EOC event
    function automatic void push_eoc_event (logic err);
        expected.push_back(err ? EVENT_EOC_ERR : EVENT_EOC);

        // ignore the last_bit if there's been an error
        if (err) begin
            expectedLastBit = 1'bx;
        end
    endfunction

    // Add events for receiving a series of full bytes of data
    function automatic void push_data_events (bit data[$]);

        foreach (data[i]) begin
            expected.push_back(data[i] ? EVENT_DATA_1 : EVENT_DATA_0);
        end

        if (data.size() != 0) begin
            if ((data.size() % 8) == 0) begin
                // expected last bit is the parity bit of the last byte
                automatic bit [7:0] lastByte;
                // unpacke the last byte of the queue into the bit vector
                {>>{lastByte}} = data[($-7):$];
                expectedLastBit = bit'(($countones(lastByte) % 2) == 0);
            end
            else begin
                // partial byte, expected last bit is the last bit
                expectedLastBit = data[$];
            end
        end
    endfunction

    // Set up an event struct for an expected error
    function automatic void push_error_event;
        expected.push_back(EVENT_ERROR);

        // don't check last_bit in case of errors
        expectedLastBit     = 1'bx;
    endfunction

    // ========================================================================
    // Check that the current event (if any) is expected
    // ========================================================================

    // build a FrameDecodeEvent struct from the outputs
    FrameDecodeEvent outputs;
    always_comb begin
        outputs.soc         = soc;
        outputs.eoc         = eoc;
        outputs.error       = error;
        outputs.data_valid  = data_valid;
        outputs.data        = data;
    end

    always_ff @(posedge clk) begin
        if (event_detected) begin
            //$display("event detected %p", outputs);

            gotEventButNoneExpected:
                assert (expected.size != 0)
                else $error("event detected but not expecting anything");

            if (expected.size != 0) begin: expectedQueueNotEmpty
                automatic FrameDecodeEvent expectedEvent = expected.pop_front;
                automatic logic expected_event_valid = validate_event(expectedEvent);

                expectedEventValid:
                    assert (expected_event_valid)
                    else $fatal(1, "An expected event was found not valid");

                eventNotAsExpected:
                    assert (outputs ==? expectedEvent)  // ==? so we allow 'x in expectedEvent as a wildcard
                    else $error("Detected event is not as expected. Got %p, expected %p",
                                outputs, expectedEvent);

                if (outputs.eoc) begin
                    // check last_bit
                    checkLastBit:
                        assert (last_bit ==? expectedLastBit) // ==? so we allow 'x in expectedLastBit as a wildcard
                        else $error("Last bit not as expected");
                end
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
             !error && !data_valid &&
             !event_detected))
        else $error("Outputs not as expected whilst in reset");

    // Check that the outputs are always valid
    logic outputs_valid;
    assign outputs_valid = validate_event(outputs);
    outputsValid:
    assert property (
        @(posedge clk)
        outputs_valid)
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

    // error is only valid for one tick at a time
    errorOnlyOneTick:
    assert property (
        @(posedge clk)
        error |=> !error)
        else $error("error asserted for more than one tick");

    // data_valid is only valid for one tick at a time
    dataValidOnlyOneTick:
    assert property (
        @(posedge clk)
        data_valid |=> !data_valid)
        else $error("data_valid asserted for more than one tick");

    // last_bit can't change after eoc until after the next soc
    lastBitStableBetweenFrames:
    assert property (
        @(posedge clk)
        $rose(eoc) |-> $stable(last_bit) throughout soc[->1])
        else $error("last_bit changed between frames");

endmodule
