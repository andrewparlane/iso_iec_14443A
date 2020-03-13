/***********************************************************************
        File: rx_interface_sink.sv
 Description: Sink for the rx_interface
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

// Note: We don't verify the prtocol here, that's done in the interface itself.
//       here we just check received events against an expected queue

module rx_interface_sink
(
    input                   clk,
    rx_interface.in_byte    iface
);

    // has something happened this tick?
    logic event_detected;
    assign event_detected = iface.soc | iface.eoc | iface.error | iface.data_valid;

    // A struct to combine the frame_decode / rx outputs
    typedef struct packed
    {
        logic                           soc;          // no other flags should be set
        logic                           eoc;          // error can be set, but no others
        logic                           error;        // eoc can be set, but no others
        logic                           data_valid;   // no other flags should be set
        logic [iface.DATA_WIDTH-1:0]    data;         // the data
        logic [2:0]                     data_bits;    // the data
    } RxEvent;

    // helper type, so we can returne a RxEvent queue from a function
    typedef RxEvent RxEventQueue [$];

    // So we can print some debug info
    function automatic string event_to_string (RxEvent e);
        automatic string res = "";
        $sformat(res, "soc %b, eoc %b, error %b, data_valid %b, data_bits %d, data %x (%b)",
                 e.soc, e.eoc, e.error, e.data_valid, e.data_bits, e.data, e.data);
        return res;
    endfunction

    // ========================================================================
    // Some functions to construct events and add them to an expected queue
    // ========================================================================

    typedef logic [iface.DATA_WIDTH-1:0] dataQueue [$];

    logic       check_expected;
    RxEvent     expected[$];;

    logic       use_receive_queue;
    dataQueue   received;

    logic       initialise_called = 1'b0;

    function automatic void initialise;
        // check by default. Better we forget to disable it than forget to enable it
        check_expected      = 1'b1;
        expected.delete;

        use_receive_queue   = 1'b0;
        received.delete;
        initialise_called   = 1'b1;
    endfunction

    initial begin: initialiseCalledCheck
        repeat(2) @(posedge clk) begin end
        initialiseCalled:
            assert (initialise_called) else $fatal(0, "Must call initialise on rx_interface_sink");
    end

    function automatic void enable_expected_checking(logic en);
        check_expected = en;
    endfunction

    function automatic void enable_receive_queue(logic en);
        use_receive_queue = en;
    endfunction

    function automatic void clear_received_queue;
        received.delete;
    endfunction

    function automatic logic received_queue_is_empty;
        return received.size == 0;
    endfunction

    function automatic dataQueue get_and_clear_received_queue;
        automatic dataQueue res = received;
        received.delete;
        return res;
    endfunction

    function automatic void clear_expected_queue;
        expected.delete;
    endfunction

    function automatic logic expected_queue_is_empty;
        return expected.size == 0;
    endfunction

    // A function to build an event struct for the SOC event
    function automatic void add_expected_soc_event;
        automatic RxEvent e;
        e.soc               = 1'b1;
        e.eoc               = 1'b0;
        e.error             = 1'b0;
        e.data_valid        = 1'b0;
        e.data_bits         = 3'dx;
        e.data              = 'x;

        expected.push_back(e);
    endfunction

    // A function to build an event struct for the EOC event
    // when the last byte is a full byte (standard frame), no data is issued
    // on the EOC event, there may however be an error.
    // This should always be used when iface.BY_BYTE == 0
    function automatic void add_expected_eoc_full_byte_event (logic err);
        automatic RxEvent e;
        e.soc               = 1'b0;
        e.eoc               = 1'b1;
        e.error             = err;
        e.data_valid        = 1'b0;
        e.data_bits         = 'x;
        e.data              = 'x;

        expected.push_back(e);
    endfunction

    // A function to build an event struct for the EOC event
    // When the last byte is not a full byte (short frame / anticollision frame)
    // then the partial byte is issued on the EOC event
    // Only for use when iface.BY_BYTE == 1
    function automatic void add_expected_eoc_part_byte_event (int num_bits, logic [iface.DATA_WIDTH-1:0] data);
        automatic RxEvent                       e;
        automatic logic [iface.DATA_WIDTH-1:0]  new_data;

        // set the none used bits as x
        new_data = data;
        for (int i = 7; i >= num_bits; i--) begin
            new_data[i] = 1'bx;
        end

        e.soc               = 1'b0;
        e.eoc               = 1'b1;
        e.error             = 1'b0;
        e.data_valid        = 1'b1;
        e.data_bits         = num_bits;
        e.data              = new_data;

        expected.push_back(e);
    endfunction

    // Add events for receiving a series of full bytes of data
    function automatic void add_expected_data_events (logic [iface.DATA_WIDTH-1:0] data[$]);

        foreach (data[i]) begin
            automatic RxEvent e;
            e.soc               = 1'b0;
            e.eoc               = 1'b0;
            e.error             = 1'b0;
            e.data_valid        = 1'b1;
            e.data_bits         = iface.BY_BYTE ? 3'd0 : 3'dx;
            e.data              = data[i];

            expected.push_back(e);
        end
    endfunction

    // Set up an event struct for an expected error
    function automatic void add_expected_error_event;
        automatic RxEvent e;
        e.soc               = 1'b0;
        e.eoc               = 1'b0;
        e.error             = 1'b1;
        e.data_valid        = 1'b0;
        e.data_bits         = 3'dx;
        e.data              = 'x;

        expected.push_back(e);
    endfunction

    function automatic void build_valid_frame_expected_queue (logic [iface.DATA_WIDTH-1:0] data[$], int bits_in_last_byte=0);
        clear_expected_queue;
        add_expected_soc_event;

        bits_in_last_byte = (bits_in_last_byte == 0) ? 8 : bits_in_last_byte;
        if ((bits_in_last_byte == 8) || !iface.BY_BYTE) begin
            add_expected_data_events(data);
            add_expected_eoc_full_byte_event(1'b0);
        end
        else begin
            if (data.size > 1) begin
                add_expected_data_events(data[0:$-1]);
            end
            add_expected_eoc_part_byte_event(bits_in_last_byte, data[$]);
        end
    endfunction

    // ========================================================================
    // Check that the current event (if any) is expected
    // ========================================================================

    // build a RxEvent struct from the iface
    RxEvent currentValues;
    always_comb begin
        currentValues.soc               = iface.soc;
        currentValues.eoc               = iface.eoc;
        currentValues.error             = iface.error;
        currentValues.data_valid        = iface.data_valid;
        currentValues.data_bits         = iface.data_bits;
        currentValues.data              = iface.data;
    end

    always_ff @(posedge clk) begin
        if (event_detected) begin
            if (check_expected) begin: checkExpected
                gotEventButNoneExpected:
                    assert (expected.size != 0)
                    else $error("event detected but not expecting anything");

                if (expected.size != 0) begin: expectedQueueNotEmpty
                    automatic RxEvent expectedEvent         = expected.pop_front;
                    automatic string err_str_actual         = event_to_string(currentValues);
                    automatic string err_str_expected       = event_to_string(expectedEvent);

                    eventNotAsExpected:
                        assert (currentValues ==? expectedEvent)  // ==? so we allow 'x in expectedEvent as a wildcard
                        else $error("Detected event is not as expected. Got %s, expected %s",
                                    err_str_actual, err_str_expected);
                end
            end

            if (use_receive_queue && iface.data_valid) begin
                received.push_back(iface.data);
            end
        end
    end

    // ========================================================================
    // Wait for the expected queue to be empty or timeout
    // ========================================================================

    task automatic wait_for_expected_empty(int timeout=0);
        fork
            // process 1, timeout
            begin
                if (timeout == 0) begin
                    forever @(posedge clk) begin end
                end
                else begin
                    repeat (timeout) @(posedge clk) begin end
                end
                $error("wait_for_expected_empty timed out after %d ticks", timeout);
            end

            // process 2 - wait for the expected queue to be empty
            begin
                wait (expected.size() == 0) begin end
            end

        // finish as soon as any of these processes finish
        join_any

        // disable the remaining process
        disable fork;
    endtask

    task automatic wait_for_idle(int timeout=0);
        fork
            // process 1, timeout
            begin
                if (timeout == 0) begin
                    forever @(posedge clk) begin end
                end
                else begin
                    repeat (timeout) @(posedge clk) begin end
                end
                $error("wait_for_idle timed out after %d ticks", timeout);
            end

            // process 2 - wait for data_valid to be low
            begin
                wait (!iface.data_valid) begin end
            end

        // finish as soon as any of these processes finish
        join_any

        // disable the remaining process
        disable fork;
    endtask

endmodule
