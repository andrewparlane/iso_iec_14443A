/***********************************************************************
        File: frame_encode_tb.sv
 Description: Testbench for the frame_encode module
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

module frame_encode_tb;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic           clk;
    logic           rst_n;

    logic           fdt_trigger;

    logic           append_crc;
    logic [15:0]    crc;

    tx_interface #(.BY_BYTE(0)) in_iface (.*);
    tx_interface #(.BY_BYTE(0)) out_iface (.*);

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    frame_encode dut (.*);

    // --------------------------------------------------------------
    // The driver / queue for the in_iface
    // --------------------------------------------------------------

    // driver
    tx_bit_iface_source_driver_pkg::TxBitIfaceSourceDriver  source_driver;

    // the send queue
    typedef tx_byte_transaction_pkg::TxByteTransaction      ByteTransType;
    typedef tx_bit_transaction_pkg::TxBitTransaction        BitTransType;
    BitTransType                                            send_queue[$];

    // --------------------------------------------------------------
    // The monitor for the out_iface
    // --------------------------------------------------------------

    tx_bit_iface_monitor_pkg::TxBitIfaceMonitor         monitor;

    // and the recv_queue
    BitTransType                                        recv_queue [$];

    // sink driver
    tx_iface_sink_driver_pkg::TxBitIfaceSinkDriver      sink_driver;

    // --------------------------------------------------------------
    // Clock generator
    // --------------------------------------------------------------

    clock_source clock_source_inst (.*);

    // --------------------------------------------------------------
    // Functions / Tasks
    // --------------------------------------------------------------

    typedef enum
    {
        ErrorType_NONE,
        ErrorType_NO_FDT,
        ErrorType_NO_SEND
    } ErrorType;

    task do_test (int num_bits, ErrorType err = ErrorType_NONE);
        automatic int           ticksBeforeFDT  = $urandom_range(16, 100);
        automatic ByteTransType byte_trans;
        automatic BitTransType  send_trans;
        automatic BitTransType  expected;

        // generate data to send (as byte trans first, in order to add the CRC)
        byte_trans = ByteTransType::new_random_transaction_bits(num_bits);

        // get the bit transaction to actually send (no CRC)
        send_trans = new(byte_trans.convert_to_bit_queue);

        // the expected transaction to receive may have a CRC
        if (append_crc) begin
            crc = byte_trans.calculate_crc;
            byte_trans.append_crc;
        end
        expected = new(byte_trans.convert_to_bit_queue);

        // and has parity bits
        expected.add_parity(num_bits % 8);

        // mark it as ready to send
        if (err != ErrorType_NO_SEND) begin
            send_queue.push_back(send_trans);
        end

        if (err != ErrorType_NO_FDT) begin
            repeat (ticksBeforeFDT) @(posedge clk) begin end
            fdt_trigger <= 1'b1;
            @(posedge clk) begin end
            fdt_trigger <= 1'b0;
        end
        else begin
            // don't fire the FDT
            // but that means our transaction will timeout
            // so disable timeout errors
            source_driver.set_enable_timeout_errors(1'b0);
        end

        // wait for idle
        source_driver.wait_for_idle;
        // could be sending the CRC = 2 bytes + parity bits = 18 bits
        // sink_driver sends reqs every 16 ticks, so 288 ticks plus extra for latency
        monitor.wait_for_idle(32, 512);

        source_driver.set_enable_timeout_errors(1'b1);

        // verify
        if (err == ErrorType_NONE) begin: noError
            receivedOneTransaction:
            assert (recv_queue.size() == 1) else $error("recv_queue.size() is %d, expecting 1", recv_queue.size());

            if (recv_queue.size() != 0) begin: recvQueueNotEmpty
                automatic BitTransType recv = recv_queue.pop_front;
                receivedExpected:
                assert (recv.compare(expected)) else $error("Received %s, not as expected %p", recv.to_string, expected.to_string);
            end
        end
        else begin: hasError
            receivedNoTransactions:
            assert (recv_queue.size() == 0) else $error("recv_queue.size() is %d, expecting 0", recv_queue.size());
        end
    endtask

    typedef enum logic [2:0]
    {
        State_IDLE,
        State_DATA,
        State_PARITY,
        State_CRC,
        State_CRC_PARITY,
        State_END
    } State;

    task do_reset_test(State state);
        automatic BitTransType  send_trans;
        send_trans = BitTransType::new_random_transaction(8);

        // we want to append the CRC, so we can get to State_CRC and State_CRC_PARITY
        append_crc = 1'b1;

        // send it
        send_queue.push_back(send_trans);

        // we don't care about timeouts
        source_driver.set_enable_timeout_errors(1'b0);

        // fire the FDT
        @(posedge clk) begin end
        fdt_trigger <= 1'b1;
        @(posedge clk) begin end
        fdt_trigger <= 1'b0;

        // wait for the dut to enter the specified state
        wait (dut.state == state) begin end
        repeat(2) @(posedge clk) begin end

        // reset
        rst_n <= 1'b0;
        @(posedge clk) begin end
        rst_n <= 1'b1;
        @(posedge clk) begin end

        repeat (5) @(posedge clk) begin end

        source_driver.wait_for_idle;
        monitor.wait_for_idle(32, 512);
    endtask

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin
        fdt_trigger <= 1'b0;
        append_crc  <= 1'b1; // set to 1 here, so when we change it to 0 later we get the toggle coverage

        // 32 ticks idle between transactions
        // 64 tick req timeout
        // 256 tick first req timeout (for the fdt timer)
        source_driver   = new(in_iface, 32, 64, 256);
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

        // don't append CRC's for now
        append_crc  = 1'b0;

        // Stuff to test
        //  1) nothing sends until fdt_trigger fires
        $display("Testing no Tx before fdt");
        repeat (100) begin
            do_test($urandom_range(1, 80), ErrorType_NO_FDT);
        end

        //  2) nothing sends if in_iface.data_valid is low when fdt_trigger fires
        $display("Testing no Tx if in_iface.data_valid not asserted on fdt_trigger");
        repeat (100) begin
            do_test(1, ErrorType_NO_SEND);
        end

        //  3) parity is correct (number of 1s is odd)
        //      - implicitly checked by adding parity bits to expected transaction

        //  4) correct number of bits are sent
        //      - implicity checked by adding all bits to the expected transaction

        // send 8 bits of data, no crc
        $display("Testing sending 8 bits");
        do_test(8);

        // send 1 - 8 bits of data, no crc
        for (int i = 1; i <= 8; i++) begin
            $display("Testing sending %d bits", i);
            do_test(i);
        end

        //  5) multiple bytes send OK, no crc
        $display("Testing multi bytes");
        repeat (1000) begin
            do_test($urandom_range(9, 80));
        end

        // 6) Test adding CRC
        // we only care about multiples of 8 bits here
        $display("Test adding CRC");
        append_crc = 1'b1;
        repeat (1000) begin
            do_test($urandom_range(1, 10)*8);
        end

        // 7) test reset forces state back to idle (mostly just for coverage)
        $display("Testing dut returns to idle on reset");

        // the driver ignores the reseet and continues trying to send
        // so ignore the assert that checks the signals are as expected in reset
        $assertoff(0, in_iface.useAsserts.signalsInReset);

        do_reset_test(State_DATA);
        do_reset_test(State_PARITY);
        do_reset_test(State_CRC);
        do_reset_test(State_CRC_PARITY);

        $asserton(0, in_iface.useAsserts.signalsInReset);

        // assert reset for toggle coverage
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

    // we should assert data_valid on the out_iface 1 tick after the fdt_trigger fires
    validAfterTrigger:
    assert property (
        @(posedge clk)
        ($rose(fdt_trigger) && in_iface.data_valid) |=>
            $rose(out_iface.data_valid))
        else $error("out_iface.data_valid didn't rise after fdt_trigger");

    // DUT returns to idle after reset
    idleAfterReset:
    assert property (
        @(posedge clk)
        $fell(rst_n) |=> (dut.state == State_IDLE))
        else $error("DUT didn't return to idle after reset");

endmodule
