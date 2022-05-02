/***********************************************************************
        File: frame_decode_tb.sv
 Description: Testbench for frame_decode
      Author: Andrew Parlane
**********************************************************************/

/*
 * This file is part of https://github.com/andrewparlane/iso_iec_14443A
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

    rx_interface #(.BY_BYTE(0)) in_iface (.*);
    rx_interface #(.BY_BYTE(0)) out_iface (.*);

    logic           last_bit;

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    frame_decode dut (.*);

    // --------------------------------------------------------------
    // The driver / queue for the in_iface
    // --------------------------------------------------------------

    // driver
    rx_bit_iface_driver_pkg::RxBitIfaceDriver           driver;

    // the send queue
    typedef rx_bit_transaction_pkg::RxBitTransaction    SendTransType;
    SendTransType                                       send_queue[$];

    // --------------------------------------------------------------
    // The monitor for the out_iface
    // --------------------------------------------------------------

    rx_bit_iface_monitor_pkg::RxBitIfaceMonitor                 monitor;

    // and the recv_queue
    typedef rx_bit_transaction_pkg::RxMonitorBitTransaction     RecvTransType;
    RecvTransType                                               recv_queue [$];

    // --------------------------------------------------------------
    // Clock generator
    // --------------------------------------------------------------

    clock_source clock_source_inst (.*);

    // --------------------------------------------------------------
    // Tasks / Functions
    // --------------------------------------------------------------

    typedef enum
    {
        ErrorType_NONE,
        ErrorType_FLIPPED_PARITY,
        ErrorType_MISSING_LAST_PARITY,
        ErrorType_INPUT_ERROR
    } ErrorType;

    logic check_last_bit;

    task do_test(int num_bits, ErrorType err = ErrorType_NONE);
        automatic SendTransType send_trans;
        automatic RecvTransType expected;
        automatic int           timeout;

        // generate the data to send without parity bits, which is what we expect to receive out.
        send_trans  = SendTransType::new_random_transaction(num_bits);
        expected    = new(send_trans.data, (err != ErrorType_NONE) || (num_bits <= 0));

        // add the parity bits
        send_trans.add_parity();

        if (err == ErrorType_MISSING_LAST_PARITY) begin: missingLastParity
            // remove the final bit
            lastBitIsParity: assert((num_bits % 8) == 0)
                else $fatal(0, "ErrorType_MISSING_LAST_PARITY can only be used when the last bit is a parity bit");
            void'(send_trans.pop_back);
        end

        if (err == ErrorType_FLIPPED_PARITY) begin
            // randomly flip a parity bit
            // every 9th bit is a parity bit
            automatic int corrupt_bit = ($urandom_range(1, (num_bits / 8)) * 9) - 1;
            send_trans.data[corrupt_bit] = !send_trans.data[corrupt_bit];
        end

        // check the last bit if we aren't expecting an error
        check_last_bit = !expected.error;

        // get the driver to add an error if requested
        driver.set_add_error(err == ErrorType_INPUT_ERROR);

        // send it
        timeout = driver.calculate_send_time(send_trans);
        send_queue.push_back(send_trans);
        monitor.wait_for_idle(16, timeout+100);

        // verify
        receivedOneTransaction:
        assert (recv_queue.size() == 1) else $error("recv_queue.size() is %d, expecting 1", recv_queue.size());

        if (recv_queue.size() != 0) begin: recvQueueNotEmpty
            automatic RecvTransType recv = recv_queue.pop_front;
            receivedExpected:
            assert (recv.compare(expected))
                else $error("Received %s, not as expected %p", recv.to_string, expected.to_string);
        end

        check_last_bit = 1'b0;
    endtask

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin
        driver      = new(in_iface);
        monitor     = new(out_iface);
        send_queue  = '{};
        recv_queue  = '{};
        driver.start(send_queue);
        monitor.start(recv_queue);

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // 1) Test an 8 bit frame with parity bit OK
        $display("Testing an 8 bit frame with parity bit OK");
        do_test(8);

        // 2) Test an 8 bit frame with parity FAIL
        $display("Testing an 8 bit frame with parity FAIL");
        do_test(8, ErrorType_FLIPPED_PARITY);

        // 3) Test an 8 bit frame with parity missing
        $display("Testing an 8 bit frame with parity bit missing");
        do_test(8, ErrorType_MISSING_LAST_PARITY);

        // 4) Test an 8 bit frame + error
        $display("Testing 8 bit frame with errors");
        repeat (1000) begin
            do_test(8, ErrorType_INPUT_ERROR);
        end

        // 5) Test 0 to 7 bit frames
        $display("Testing 0 to 7 bit frames");
        for (int i = 0; i <= 7; i++) begin
            do_test(i);
        end

        // 7) Test an N bit frame with parity OK
        $display("Testing random length frames");
        repeat (1000) begin
            do_test($urandom_range(1, 80));
        end

        // 8) Test an N bit frame with parity FAIL
        $display("Testing random length frames with parity fail");
        repeat (1000) begin
            do_test($urandom_range(8, 80), ErrorType_FLIPPED_PARITY);
        end

        // 9) Test an N byte frame with last parity missing
        $display("Testing frames with missing last parity bit");
        repeat (1000) begin
            //$display("Testing a %d byte frame with last parity missing", num_bytes);
            do_test($urandom_range(1, 10)*8, ErrorType_MISSING_LAST_PARITY);
        end

        // assert reset for toggle coverage
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

    // VCS doesn't like disable iff (!rst_n)
    logic rst;
    assign rst = !rst_n;

    // check last_bit is correct on eoc rising
    lastBitCorrect:
    assert property (
        @(posedge clk)
        ($rose(out_iface.eoc) && check_last_bit) |=>
            (last_bit == in_iface.data))
        else $error("last_bit is %b, expected %b", last_bit, in_iface.data);

    // last_bit can't change after eoc until after the next soc
    lastBitStableBetweenFrames:
    assert property (
        @(posedge clk)
        disable iff (rst)
        $rose(out_iface.eoc) |=> $stable(last_bit) throughout out_iface.soc[->1])
        else $error("last_bit changed between frames");

endmodule
