/***********************************************************************
        File: serialiser_tb.sv
 Description: Testbench for serialiser
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

module serialiser_tb;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic           clk;
    logic           rst_n;

    tx_interface #(.BY_BYTE(1)) in_iface (.*);
    tx_interface #(.BY_BYTE(0)) out_iface (.*);

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    serialiser dut (.*);

    // --------------------------------------------------------------
    // The driver / queue for the in_iface
    // --------------------------------------------------------------

    // driver
    tx_byte_iface_source_driver_pkg::TxByteIfaceSourceDriver    source_driver;

    // the send queue
    typedef tx_byte_transaction_pkg::TxByteTransaction          SendTransType;
    SendTransType                                               send_queue[$];

    // --------------------------------------------------------------
    // The monitor for the out_iface
    // --------------------------------------------------------------

    tx_bit_iface_monitor_pkg::TxBitIfaceMonitor         monitor;

    // and the recv_queue
    typedef tx_bit_transaction_pkg::TxBitTransaction    RecvTransType;
    RecvTransType                                       recv_queue [$];

    // sink driver
    tx_iface_sink_driver_pkg::TxBitIfaceSinkDriver      sink_driver;

    // --------------------------------------------------------------
    // Clock generator
    // --------------------------------------------------------------

    clock_source clock_source_inst (.*);

    // --------------------------------------------------------------
    // Tasks
    // --------------------------------------------------------------

    task send_data_verify_result (int num_bits);
        automatic SendTransType     byte_trans;
        automatic RecvTransType     expected;

        // generate byte transaction first (what we send)
        byte_trans = SendTransType::new_random_transaction_bits(num_bits);

        // get the expected
        expected    = new(byte_trans.convert_to_bit_queue);

        // send it
        send_queue.push_back(byte_trans);

        // wait for it to be done
        source_driver.wait_for_idle();
        monitor.wait_for_idle(16, 32);

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
        source_driver   = new(in_iface, 32, 256);
        sink_driver     = new(out_iface);
        monitor         = new(out_iface);
        send_queue      = '{};
        recv_queue      = '{};
        source_driver.start(send_queue);
        sink_driver.start();
        monitor.start(recv_queue);

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // 1) Test 1 - 16 bit frames
        $display("Testing 1-16 bit frames");
        for (int i = 1; i <= 16; i++) begin
            send_data_verify_result(i);
        end

        // 2) send lots of random frames
        $display("Testing lots of frames");
        repeat (1000) begin
            send_data_verify_result($urandom_range(1,80));
        end

        // assert reset for toggle coverage
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

endmodule
