/***********************************************************************
        File: deserialiser_tb.sv
 Description: Testbench for deserialiser
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

module deserialiser_tb;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic           clk;
    logic           rst_n;

    rx_interface #(.BY_BYTE(0)) in_iface (.*);
    rx_interface #(.BY_BYTE(1)) out_iface (.*);

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    deserialiser dut (.*);

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

    rx_byte_iface_monitor_pkg::RxByteIfaceMonitor               monitor;

    // and the recv_queue
    typedef rx_byte_transaction_pkg::RxMonitorByteTransaction   RecvTransType;
    RecvTransType                                               recv_queue [$];

    // --------------------------------------------------------------
    // Clock generator
    // --------------------------------------------------------------

    clock_source clock_source_inst (.*);

    // --------------------------------------------------------------
    // Helper functions / tasks
    // --------------------------------------------------------------

    task send_data_verify_result(int num_bits, logic add_error=1'b0);
        automatic SendTransType trans;
        automatic RecvTransType expected;
        automatic int           timeout;
        // generate byte transaction first
        expected = RecvTransType::new_random_transaction_bits(num_bits, add_error);

        // get the bit transaction (to send)
        trans = new(expected.convert_to_bit_queue);

        // send it
        driver.set_add_error(add_error);
        timeout = driver.calculate_send_time(trans);
        send_queue.push_back(trans);

        // wait for it to be done
        monitor.wait_for_idle(15, timeout + 100);
        driver.set_add_error(1'b0);

        // verify
        receivedOneTransaction:
        assert (recv_queue.size() == 1) else $error("recv_queue.size() is %d, expecting 1", recv_queue.size());

        if (recv_queue.size() != 0) begin: recvQueueNotEmpty
            automatic RecvTransType recv = recv_queue.pop_front;
            receivedExpected:
            assert (recv.compare(expected)) else $error("Received %s, not as expected %p", recv.to_string, expected.to_string);
        end
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

        // 1) Test 0 - 16 bit frames
        $display("Testing 0-16 bit frames");
        for (int i = 0; i <= 16; i++) begin
            send_data_verify_result(i);
        end

        // 2) send lots of random frames
        $display("Testing lots of frames");
        repeat (1000) begin
            send_data_verify_result($urandom_range(80));
        end

        // 3) send lots of random frames with errors
        $display("Testing frames with errors");
        repeat (1000) begin
            send_data_verify_result($urandom_range(80), 1'b1);
        end

        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

endmodule
