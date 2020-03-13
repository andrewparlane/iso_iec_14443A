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
    tx_interface.in_all     iface
);

    typedef logic [iface.DATA_WIDTH-1:0] dataQueue [$];

    logic       check_expected;
    dataQueue   expected;

    logic       check_last_bit_in_byte;
    logic       last_bit_in_byte_expected [$];

    logic       use_receive_queue;
    dataQueue   received;

    int         bits_in_first_byte;

    logic       initialise_called = 1'b0;

    function automatic void initialise;
        iface.req               = 1'b0;

        // check by default. Better we forget to disable it than forget to enable it
        check_expected          = 1'b1;
        expected.delete;

        check_last_bit_in_byte  = 1'b0;
        last_bit_in_byte_expected.delete;

        use_receive_queue       = 1'b0;
        received.delete;
        initialise_called       = 1'b1;
    endfunction

    initial begin: initialiseCalledCheck
        repeat(2) @(posedge clk) begin end
        initialiseCalled:
            assert (initialise_called) else $fatal(0, "Must call initialise on tx_interface_sink");
    end

    function automatic void clear_expected_queue;
        expected.delete;
        last_bit_in_byte_expected.delete;
    endfunction

    function automatic void clear_received_queue;
        received.delete;
    endfunction

    function automatic void set_expected_queue(logic [iface.DATA_WIDTH-1:0] data[$],
                                               logic last_bit_in_bytes [$] ='{});
        expected                    = data;
        last_bit_in_byte_expected   = last_bit_in_bytes;
    endfunction

    function automatic dataQueue get_and_clear_received_queue;
        automatic dataQueue res = received;
        received.delete;
        return res;
    endfunction

    function automatic int get_bits_in_first_byte;
        return bits_in_first_byte;
    endfunction

    function automatic logic expected_queue_is_empty;
        return (expected.size == 0) && (last_bit_in_byte_expected.size == 0);
    endfunction

    function automatic logic received_queue_is_empty;
        return received.size == 0;
    endfunction

    function automatic void enable_expected_checking(logic en, last_bit_checking=1'b0);
        check_expected          = en;
        check_last_bit_in_byte  = last_bit_checking;
    endfunction

    function automatic void enable_receive_queue(logic en);
        use_receive_queue = en;
    endfunction

    initial begin: sinkInitial
        automatic logic first_tfer = 1'b1;
        automatic logic first_byte = 1'b1;
        iface.req <= 1'b0;

        forever begin: foreverLoop
            // if data_valid is currently low, then this frame is done
            // and we are waiting for the next
            if (!iface.data_valid) begin
                first_tfer = 1'b1;
                first_byte = 1'b1;
            end

            // wait for data_valid to assert
            wait (iface.data_valid) begin end

            // sameple the data
            //$display("got: %b, last_bit_in_byte %b", iface.data, iface.last_bit_in_byte);

            if (first_tfer) begin: firstTfer
                // this is the first bit / byte that we've receive check our
                // receive queue is empty. Otherwise we'll merge two packets.
                if (use_receive_queue) begin: usingRxQueue
                    rxQueueEmpty:
                    assert (received.size() == 0) else $error("Received queue not empty on receiving the first byte of a new frame");
                end
                first_tfer          = 1'b0;
            end
            else begin: notFirstTfer
                if (iface.BY_BYTE) begin: byByte
                    // only the first byte may be a partial byte
                    partialByteCheck:
                    assert (iface.data_bits == 0) else $error("Partial byte in the middle of a Tx frame");
                end
            end

            if (first_byte) begin
                if (iface.BY_BYTE) begin
                    // we've got valid data for our first byte
                    // save the number of bits in this first byte
                    bits_in_first_byte  = int'(iface.data_bits);
                    first_byte          = 1'b0;
                end
                else begin
                    // we're by bit. We know that the last bit occurs when
                    // last_bit_in_byte is set, so just count the bits until then.
                    bits_in_first_byte++;
                    if (iface.last_bit_in_byte) begin
                        first_byte = 1'b0;
                    end
                end
            end

            // add it to the receive queue
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

            // check against the last_bit_in_byte_expected queue
            if (check_last_bit_in_byte) begin: checkLastBitInByteExpected
                expectedNotEmpty:
                assert(last_bit_in_byte_expected.size() != 0)
                    else $error("last_bit_in_byte_expected queue empty, but received data");

                if ((last_bit_in_byte_expected.size() != 0)) begin: checkingBlock
                    automatic logic e = last_bit_in_byte_expected.pop_front;
                    lastBitInByteAsExpected:
                    assert (iface.last_bit_in_byte == e)
                        else $error("last_bit_in_byte expected %b got %b", e, iface.last_bit_in_byte);
                end
            end

            // wait a few ticks before requesting more data
            // we could end up with errors if in the real design upstream requests
            // data quicker than this. But we should see that in the top level testbench
            // at the worst.
            // Adittionally I don't think anything ever requests anything more frequently than
            // every 64 ticks
            repeat(4) @(posedge clk) begin end

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
