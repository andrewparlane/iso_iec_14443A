/***********************************************************************
        File: framing_tb.sv
 Description: Testbench for framing
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

module framing_tb;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic                       clk;
    logic                       rst_n;

    logic                       pause_n_synchronised;

    rx_interface #(.BY_BYTE(0)) in_rx_iface (.*);
    rx_interface #(.BY_BYTE(0)) out_rx_iface_bits (.*);
    rx_interface #(.BY_BYTE(1)) out_rx_iface_bytes (.*);
    logic                       rx_crc_ok;

    tx_interface #(.BY_BYTE(1)) in_tx_iface (.*);
    logic                       tx_append_crc;

    tx_interface #(.BY_BYTE(0)) out_tx_iface (.*);

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    localparam TIMING_ADJUST = 1100;    // 1100 to speed up the simulation

    framing
    #(
        .FDT_TIMING_ADJUST(TIMING_ADJUST)
    )
    dut (.*);

    // --------------------------------------------------------------
    // Clock generator
    // --------------------------------------------------------------

    // Using 10MHz clock, so we can work with an integer period
    // avoiding timing errors generated due to the simulator only having ps accuracy
    // note: this won't be an issue in synthesis
    localparam real CLOCK_FREQ_HZ = 10000000.0; // 10MHz
    clock_source
    #(
        .CLOCK_FREQ_HZ (CLOCK_FREQ_HZ)
    )
    clock_source_inst (.*);

    localparam real CLOCK_PERIOD_PS = 1000000000000.0 / CLOCK_FREQ_HZ;

    // --------------------------------------------------------------
    // The driver / queue for the in_rx_iface
    // --------------------------------------------------------------

    // driver
    rx_bit_iface_driver_pkg::RxBitIfaceDriver           rx_driver;

    // the send queue
    typedef rx_byte_transaction_pkg::RxByteTransaction  RxByteTransType;
    typedef rx_bit_transaction_pkg::RxBitTransaction    RxSendTransType;
    RxSendTransType                                     rx_send_queue[$];

    // --------------------------------------------------------------
    // The monitors for the out_rx_iface_*
    // --------------------------------------------------------------

    rx_bit_iface_monitor_pkg::RxBitIfaceMonitor                 rx_bit_monitor;
    rx_byte_iface_monitor_pkg::RxByteIfaceMonitor               rx_byte_monitor;

    // and the recv_queue
    typedef rx_bit_transaction_pkg::RxMonitorBitTransaction     RxRecvBitTransType;
    typedef rx_byte_transaction_pkg::RxMonitorByteTransaction   RxRecvByteTransType;
    RxRecvBitTransType                                          rx_recv_bit_queue   [$];
    RxRecvByteTransType                                         rx_recv_byte_queue  [$];

    // --------------------------------------------------------------
    // The driver / queue for the in_tx_iface
    // --------------------------------------------------------------

    // driver
    tx_byte_iface_source_driver_pkg::TxByteIfaceSourceDriver    tx_source_driver;

    // the send queue
    typedef tx_byte_transaction_pkg::TxByteTransaction          TxSendTransType;
    TxSendTransType                                             tx_send_queue[$];

    // --------------------------------------------------------------
    // The monitor and sink driver for the out_tx_iface
    // --------------------------------------------------------------

    tx_bit_iface_monitor_pkg::TxBitIfaceMonitor         tx_monitor;

    // and the recv_queue
    typedef tx_bit_transaction_pkg::TxBitTransaction    TxRecvTransType;
    TxRecvTransType                                     tx_recv_queue [$];

    // sink driver
    tx_iface_sink_driver_pkg::TxBitIfaceSinkDriver      tx_sink_driver;

    // --------------------------------------------------------------
    // FDT verification
    // --------------------------------------------------------------

    // Timings, from ISO/IEC 14443-3:2016 section 6.2.1.1
    localparam int FDT_LAST_BIT_0 = 1172 - TIMING_ADJUST;
    localparam int FDT_LAST_BIT_1 = 1236 - TIMING_ADJUST;

    // measure the time between the rising edge of pause_n_synchronised
    // and the rising edge of data_valid

    // this is a time in ps (`timescale)
    longint lastPauseRise;
    always_ff @(posedge pause_n_synchronised) lastPauseRise <= $time;

    logic last_rx_bit;
    always_ff @(posedge out_tx_iface.data_valid) begin: triggerBlock
        // tx has started
        automatic longint diff = $time - lastPauseRise;
        automatic longint expected = CLOCK_PERIOD_PS * (last_rx_bit ? FDT_LAST_BIT_1 : FDT_LAST_BIT_0);
        //$display("Tx started at %d ps, lastPauseRise %d ps, diff %d ps (%d ticks), expected %d ps (%d ticks)",
        //         $time, lastPauseRise, diff, int'(diff / CLOCK_PERIOD_PS), expected, int'(expected / CLOCK_PERIOD_PS));

        fdtTime: assert (diff == expected)
            else $error("Tx started at %d ps, lastPauseRise %d ps, diff %d, expected %d",
                        $time, lastPauseRise, diff, expected);
    end

    // --------------------------------------------------------------
    // Tasks and functions
    // --------------------------------------------------------------

    typedef enum
    {
        RxErrorType_NONE,
        RxErrorType_FLIPPED_PARITY,
        RxErrorType_MISSING_LAST_PARITY,
        RxErrorType_INPUT_ERROR,
        RxErrorType_CORRUPT_DATA
    } RxErrorType;

    logic check_rx_crc_ok;
    logic expect_rx_crc_ok;

    task send_rx_frame (int num_bits, RxErrorType err = RxErrorType_NONE);
        automatic RxByteTransType       byte_trans;
        automatic RxSendTransType       send_trans;
        automatic RxRecvByteTransType   expected_bytes;
        automatic RxRecvBitTransType    expected_bits;
        automatic int                   timeout;
        automatic logic                 expect_frame_error;

        // We expect a frame error if err is anything other than none or corrupt_data
        // in the corrupt_data case we expect the rx_crc_ok to be 1'b0
        expect_frame_error = !((err == RxErrorType_NONE) ||
                               (err == RxErrorType_CORRUPT_DATA));

        // generate the transaction as an RxByteTransaction
        byte_trans = RxByteTransType::new_random_transaction_bits(num_bits);

        // only check rx_crc_ok if we add the CRC to the data
        check_rx_crc_ok = 1'b0;

        // add the CRC if sending a whole number of bytes
        if ((num_bits % 8) == 0) begin
            byte_trans.append_crc;
            num_bits            += 16;                      // so we can use num_bits later
            check_rx_crc_ok     = !expect_frame_error;      // don't check if there going to be a frame error
            expect_rx_crc_ok    = err == RxErrorType_NONE;
        end

        // corrupt the data?
        if (err == RxErrorType_CORRUPT_DATA) begin
            automatic int idx               = $urandom_range(num_bits-1);
            byte_trans.data[idx/8][idx%8]   = !byte_trans.data[idx/8][idx%8];
        end

        // the out_rx_iface_bytes should receive the byte_trans
        expected_bytes  = new(byte_trans.data,
                              byte_trans.bits_in_last_byte,
                              expect_frame_error);

        // get the bit transaction that we're going to send, we'll add parity bits to this later
        send_trans      = new(byte_trans.convert_to_bit_queue);

        // the out_rx_iface_bits should receive the send_trans without the parity bits
        expected_bits   = new(send_trans.data,
                              expect_frame_error);

        // add the parity bits to our send transaction
        send_trans.add_parity;

        if (err == RxErrorType_MISSING_LAST_PARITY) begin: missingLastParity
            // remove the final bit
            lastBitIsParity: assert((num_bits % 8) == 0)
                else $fatal(0, "RxErrorType_MISSING_LAST_PARITY can only be used when the last bit is a parity bit");
            void'(send_trans.pop_back);
        end

        if (err == RxErrorType_FLIPPED_PARITY) begin
            // randomly flip a parity bit
            // there are num_bits / 8 (rounded down) full bytes, hence num_bits / 8 parity bits.
            // every 9th bit is a parity bit
            automatic int corrupt_bit = ($urandom_range(1, (num_bits / 8)) * 9) - 1;
            send_trans.data[corrupt_bit] = !send_trans.data[corrupt_bit];
        end

        // send it
        last_rx_bit = send_trans.data[$];
        timeout     = rx_driver.calculate_send_time(send_trans);
        rx_driver.set_add_error(err == RxErrorType_INPUT_ERROR);
        rx_send_queue.push_back(send_trans);
        rx_bit_monitor.wait_for_idle(16, timeout+100);
        rx_byte_monitor.wait_for_idle(16, 32);

        // verify byte out iface
        receivedOneByteTransaction:
        assert (rx_recv_byte_queue.size() == 1) else $error("rx_recv_byte_queue.size() is %d, expecting 1", rx_recv_byte_queue.size());

        if (rx_recv_byte_queue.size() != 0) begin: recvByteQueueNotEmpty
            automatic RxRecvByteTransType recv = rx_recv_byte_queue.pop_front;
            receivedExpected:
            assert (recv.compare(expected_bytes))
                else $error("Received %s, not as expected %p", recv.to_string, expected_bytes.to_string);
        end

        // verify bit out iface
        receivedOneBitTransaction:
        assert (rx_recv_bit_queue.size() == 1) else $error("rx_recv_bit_queue.size() is %d, expecting 1", rx_recv_bit_queue.size());

        if (rx_recv_bit_queue.size() != 0) begin: recvBitQueueNotEmpty
            automatic RxRecvBitTransType recv = rx_recv_bit_queue.pop_front;
            receivedExpected:
            assert (recv.compare(expected_bits))
                else $error("Received %s, not as expected %p", recv.to_string, expected_bits.to_string);
        end
    endtask

    // note: we'll never add the crc if num_bits is not a whole byte
    task send_tx_frame (int num_bits, logic add_crc);
        automatic TxSendTransType send_trans;
        automatic TxSendTransType expected_bytes;
        automatic TxRecvTransType expected;

        // generate a random byte transaction of length num_bits
        send_trans = TxSendTransType::new_random_transaction_bits(num_bits);

        // generate expected transaction based on send_trans
        // start with a byte transaction, so we can append the CRC if required
        expected_bytes = new(send_trans.data, send_trans.bits_in_first_byte);

        // the crc only gets added if add_crc and bits_in_first_byte == 0
        tx_append_crc <= 1'b0;
        if (((num_bits % 8) == 0) && add_crc) begin
            tx_append_crc <= 1'b1;
            expected_bytes.append_crc;
        end

        // now we get the actual expected data as a bit transaction, and add the parity bits
        expected = new(expected_bytes.convert_to_bit_queue);
        expected.add_parity(expected_bytes.bits_in_first_byte);

        // The frame_encoder will never send until it gets the FDT trigger
        // which means we have to set the FDT timer running by pulsing pause_n_synchronised
        pause_n_synchronised <= 1'b0;
        @(posedge clk) begin end
        pause_n_synchronised <= 1'b1;

        // send it
        tx_send_queue.push_back(send_trans);
        tx_source_driver.wait_for_idle();
        tx_monitor.wait_for_idle(32, 512);

        // verify
        receivedOneTransaction:
        assert (tx_recv_queue.size() == 1) else $error("tx_recv_queue.size() is %d, expecting 1", tx_recv_queue.size());

        if (tx_recv_queue.size() != 0) begin: recvQueueNotEmpty
            automatic TxRecvTransType recv = tx_recv_queue.pop_front;
            receivedExpected:
            assert (recv.compare(expected)) else $error("Received %s, not as expected %p", recv.to_string, expected.to_string);
        end
    endtask

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin

        rx_driver           = new(in_rx_iface);
        rx_bit_monitor      = new(out_rx_iface_bits);
        rx_byte_monitor     = new(out_rx_iface_bytes);
        // timeout between reqs is 256, to allow for an entire byte + parity to be sent out as bits
        // timeout on first req is 512, to allow for the FDT
        tx_source_driver    = new(in_tx_iface, 32, 256, 512);
        tx_sink_driver      = new(out_tx_iface);
        tx_monitor          = new(out_tx_iface);

        rx_send_queue       = '{};
        rx_recv_bit_queue   = '{};
        rx_recv_byte_queue  = '{};
        tx_send_queue       = '{};
        tx_recv_queue       = '{};

        rx_driver.start         (rx_send_queue);
        rx_bit_monitor.start    (rx_recv_bit_queue);
        rx_byte_monitor.start   (rx_recv_byte_queue);
        tx_source_driver.start  (tx_send_queue);
        tx_sink_driver.start    ();
        tx_monitor.start        (tx_recv_queue);

        pause_n_synchronised    = 1'b1;
        tx_append_crc           = 1'b0;

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // 1) rx + CRC
        $display("Testing Rx + CRC");
        repeat (1000) send_rx_frame($urandom_range(1, 10) * 8);

        // 2) rx ending in partial byte (no CRC)
        $display("Testing Rx ending with partial bytes");
        repeat (1000) send_rx_frame(($urandom_range(1, 10) * 8) + $urandom_range(1, 7));

        // 3) rx + CRC corrupted (bits and bytes)
        $display("Testing Rx + CRC with corrupted data");
        repeat (1000) send_rx_frame($urandom_range(1, 10) * 8, RxErrorType_CORRUPT_DATA);

        // 4) rx with a flipped parity bit
        $display("Testing Rx with a flipped parity bit");
        repeat (1000) send_rx_frame($urandom_range(8, 80), RxErrorType_FLIPPED_PARITY);

        // 5) rx with missing last parity bit
        $display("Testing Rx with a missing last parity bit");
        repeat (1000) send_rx_frame($urandom_range(1, 10)*8, RxErrorType_MISSING_LAST_PARITY);

        // 6) rx with input errors
        $display("Testing Rx with input errors");
        repeat (1000) send_rx_frame($urandom_range(1, 80), RxErrorType_INPUT_ERROR);

        // prepare for Tx by sending a small valid Rx frame, so that last_rx_bit will be correct
        send_rx_frame(1);

        // 7) tx without CRC (partial bytes + whole bytes)
        $display("Testing Tx without CRC");
        repeat (1000) send_tx_frame($urandom_range(1, 80), 1'b0);

        // 8) tx with CRC
        $display("Testing Tx + CRC");
        repeat (1000) send_tx_frame(($urandom_range(1, 10) * 8), 1'b1);

        // 9) FDT time
        // note that we test the FDT time in all the above cases too
        // but since we do all the Rx and then all the Tx, rx_last_bit is constant (per sim)
        // so we don another 1000 runs here, where rx_last_bit should toggle randomly
        $display("Testing FDT time");
        repeat (1000) begin
            // send a small rx frame so that rx_last_bit changes
            send_rx_frame($urandom_range(1,16));
            // send a small tx frame
            send_tx_frame($urandom_range(1,16), 1'b0);
        end

        // assert reset for toggle coverage
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // check rx_crc_ok as expected on EOC
    rxCrcOkAsExpectedBits:
    assert property (
        @(posedge clk)
        ($rose(out_rx_iface_bits.eoc) && check_rx_crc_ok) |-> (rx_crc_ok == expect_rx_crc_ok))
        else $error("rx_crc_ok (%b) not as expected", rx_crc_ok);

    rxCrcOkAsExpectedBytes:
    assert property (
        @(posedge clk)
        ($rose(out_rx_iface_bytes.eoc) && check_rx_crc_ok) |-> (rx_crc_ok == expect_rx_crc_ok))
        else $error("rx_crc_ok (%b) not as expected", rx_crc_ok);


endmodule
