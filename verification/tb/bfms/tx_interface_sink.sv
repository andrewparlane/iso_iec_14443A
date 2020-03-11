/***********************************************************************
        File: tx_interface_sink.sv
 Description: Sink for the tx_interface
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

module tx_interface_sink
(
    input                   clk,
    tx_interface.in_byte    iface
);

    typedef logic [iface.DATA_WIDTH-1:0] dataQueue [$];

    logic       check_expected;
    dataQueue   expected;

    logic       use_receive_queue;
    dataQueue   received;

    function automatic void initialise;
        iface.req           = 1'b0;

        // check by default. Better we forget to disable it than forget to enable it
        check_expected      = 1'b1;
        expected.delete;

        use_receive_queue   = 1'b0;
        received.delete;
    endfunction

    function automatic void clear_expected_queue;
        expected.delete;
    endfunction

    function automatic void clear_received_queue;
        received.delete;
    endfunction

    function automatic void set_expected_queue(logic [iface.DATA_WIDTH-1:0] data[$]);
        expected = data;
    endfunction

    function automatic dataQueue get_and_clear_received_queue;
        automatic dataQueue res = received;
        received.delete;
        return res;
    endfunction

    function automatic logic expected_queue_is_empty;
        return expected.size == 0;
    endfunction

    function automatic logic received_queue_is_empty;
        return received.size == 0;
    endfunction

    function automatic void enable_expected_checking(logic en);
        check_expected = en;
    endfunction

    function automatic void enable_receive_queue(logic en);
        use_receive_queue = en;
    endfunction

    initial begin: sinkInitial
        iface.req <= 1'b0;

        forever begin: foreverLoop
            // wait for data_valid to assert
            wait (iface.data_valid) begin end

            // sameple the data
            //$display("got: %b", iface.data);
            if (use_receive_queue) begin
                received.push_back(iface.data);
            end

            // check against the expected queue
            if (check_expected) begin: checkExpected
                expectedNotEmpty:
                assert(expected.size() != 0) else $error("expected queue empty, but received data");

                if ((expected.size() != 0)) begin: checkingBlock
                    automatic logic [iface.DATA_WIDTH-1:0] e = expected.pop_front;
                    dataAsExpected:
                    assert (iface.data == e) else $error("Expected %x got %x", e, iface.data);
                end
            end

            // wait a few ticks before requesting more data
            repeat(2) @(posedge clk) begin end

            // request more data
            iface.req <= 1'b1;
            @(posedge clk) begin end
            iface.req <= 1'b0;
            @(posedge clk) begin end

            // wait a few ticks for the data to be updated
            repeat(6) @(posedge clk) begin end
        end
    end

    // ========================================================================
    // Timeouts
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

    task automatic wait_for_rx_complete(int timeout=0);
        fork
            // process 1, timeout
            begin
                if (timeout == 0) begin
                    forever @(posedge clk) begin end
                end
                else begin
                    repeat (timeout) @(posedge clk) begin end
                end
                $error("wait_for_rx_complete timed out after %d ticks", timeout);
            end

            // process 2 - wait for the rx to be complete
            begin
                // first we wait for the data to be valid (started sending
                wait (iface.data_valid) begin end
                // then we wait for it to no longer be valid (finished sending)
                wait (!iface.data_valid) begin end
            end

        // finish as soon as any of these processes finish
        join_any

        // disable the remaining process
        disable fork;
    endtask

endmodule
