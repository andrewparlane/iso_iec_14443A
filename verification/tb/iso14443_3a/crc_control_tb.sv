/***********************************************************************
        File: crc_control_tb
 Description: Testbench for crc_control
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

module crc_control_tb;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic           clk;
    logic           rst_n;

    logic           rx_crc_ok;

    logic           tx_append_crc;  // we only calculate the Tx CRC if we will use it
    logic           fdt_trigger;    // we only start the CRC calculation on the fdt_trigger for Tx
    logic [15:0]    crc;

    // interface
    rx_interface #(.BY_BYTE(0)) rx_iface (.*);
    tx_interface #(.BY_BYTE(0)) tx_iface (.*);

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    crc_control dut (.*);

    // --------------------------------------------------------------
    // The driver / queue for the rx_iface
    // --------------------------------------------------------------

    // driver
    rx_bit_iface_driver_pkg::RxBitIfaceDriver           rx_driver;

    // the send queue
    typedef queue_transaction_pkg::ByteQueueTransaction ByteTransType;
    typedef rx_bit_transaction_pkg::RxBitTransaction    RxTransType;
    RxTransType                                         rx_send_queue[$];

    // --------------------------------------------------------------
    // The driver / queue for the tx_iface
    // --------------------------------------------------------------

    // source driver
    tx_bit_iface_source_driver_pkg::TxBitIfaceSourceDriver  tx_source_driver;
    // sink driver (drives req, because the crc_control snoops the tx bus)
    tx_iface_sink_driver_pkg::TxIfaceSinkDriver
    #(
        .IfaceType(virtual tx_interface #(.BY_BYTE(0)))
    )
    tx_sink_driver;

    // the send queue
    typedef tx_bit_transaction_pkg::TxBitTransaction        TxTransType;
    TxTransType                                             tx_send_queue[$];

    // --------------------------------------------------------------
    // Clock generator
    // --------------------------------------------------------------

    clock_source clock_source_inst (.*);

    // --------------------------------------------------------------
    // Functions / Tasks
    // --------------------------------------------------------------

    task add_rx_data (ByteTransType byte_trans, inout int timeout, input corrupt_random_bit=1'b0);
        automatic RxTransType   bit_trans       = new (byte_trans.convert_to_bit_queue);
        automatic int           corrupt_bit_idx = $urandom_range(bit_trans.size()-1);

        if (corrupt_random_bit) begin
            bit_trans.data[corrupt_bit_idx] = !bit_trans.data[corrupt_bit_idx];
        end

        timeout += rx_driver.calculate_send_time(bit_trans);
        rx_send_queue.push_back(bit_trans);
    endtask

    // we need a task to send tx data, since we need to fire the fdt
    task send_tx_data (ByteTransType byte_trans, logic fire_fdt=1'b1);
        automatic TxTransType trans = new(byte_trans.convert_to_bit_queue);
        tx_send_queue.push_back(trans);

        if (fire_fdt) begin
            // fire FDT once data is ready to send
            wait(tx_iface.data_valid) begin end
            @(posedge clk) begin end
            fdt_trigger <= 1'b1;
            @(posedge clk) begin end
            fdt_trigger <= 1'b0;
        end

        // wait for the data to have been sent
        tx_source_driver.wait_for_idle();   // guaranteed to go idle due to internal timeout
    endtask

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------
    logic           check_rx_crc_ok;
    logic           expect_rx_crc_ok;
    logic           check_tx_crc;
    logic [15:0]    expected_crc;
    logic           check_crc_stable;

    initial begin: testStimulus
        automatic ByteTransType byte_trans;
        automatic int           timeout;

        rx_driver           = new(rx_iface);
        tx_source_driver    = new(tx_iface);
        tx_sink_driver      = new(tx_iface);

        rx_send_queue       = '{};
        tx_send_queue       = '{};

        rx_driver.start(rx_send_queue);
        tx_source_driver.start(tx_send_queue);
        tx_sink_driver.start();

        check_tx_crc        = 1'b0;
        check_rx_crc_ok     = 1'b0;
        check_crc_stable    = 1'b0;

        tx_append_crc       = 1'b0;
        fdt_trigger         = 1'b0;

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // 1) rx_crc_ok after receiving:
        //  a) 8'h00, 8'h00, 8'hA0, 8'h1E   - given as an example in ISO/IEC 14443-3:2016 Annex B
        //  b) 8'h12, 8'h34, 8'h26, 8'hCF   - given as an example in ISO/IEC 14443-3:2016 Annex B
        //  c) 8'h63, 8'h63                 - inial CRC value for no data

        $display("Testing Rx with annex B examples");
        expect_rx_crc_ok    = 1'b1;
        check_rx_crc_ok     = 1'b1;
        check_tx_crc        = 1'b0;
        check_crc_stable    = 1'b0;

        timeout             = 0;

        byte_trans          = new('{8'h00, 8'h00, 8'hA0, 8'h1E});
        add_rx_data(byte_trans, timeout);

        byte_trans          = new('{8'h12, 8'h34, 8'h26, 8'hCF});
        add_rx_data(byte_trans, timeout);

        byte_trans          = new('{8'h63, 8'h63});
        add_rx_data(byte_trans, timeout);

        rx_driver.wait_for_idle(timeout + 100);
        repeat (5) @(posedge clk) begin end

        // 2) rx_crc_ok after sending random messages with CRC

        $display("Testing random Rx with valid CRC");
        expect_rx_crc_ok    = 1'b1;
        check_rx_crc_ok     = 1'b1;
        check_tx_crc        = 1'b0;
        check_crc_stable    = 1'b0;

        timeout             = 0;

        repeat (1000) begin
            byte_trans = ByteTransType::new_random_transaction($urandom_range(0, 10));
            byte_trans.append_crc;
            add_rx_data(byte_trans, timeout);
        end
        rx_driver.wait_for_idle(timeout + 100);
        repeat (5) @(posedge clk) begin end

        // 3) !rx_crc_ok after corrupting random bit in message

        $display("Testing random Rx with invalid CRC");
        expect_rx_crc_ok    = 1'b0;
        check_rx_crc_ok     = 1'b1;
        check_tx_crc        = 1'b0;
        check_crc_stable    = 1'b0;

        timeout             = 0;

        repeat (1000) begin
            byte_trans = new();
            byte_trans = ByteTransType::new_random_transaction($urandom_range(0, 10));
            byte_trans.append_crc;

            add_rx_data(byte_trans, timeout, 1'b1);
        end

        rx_driver.wait_for_idle(timeout + 100);
        repeat (5) @(posedge clk) begin end

        // 4) crc correct after sending:
        //  a) 8'h00, 8'h00                 - given as an example in ISO/IEC 14443-3:2016 Annex B
        //  b) 8'h12, 8'h34                 - given as an example in ISO/IEC 14443-3:2016 Annex B

        $display("Testing Tx with annex B examples");
        check_rx_crc_ok     = 1'b0;
        check_tx_crc        = 1'b1;
        tx_append_crc       = 1'b1;
        check_crc_stable    = 1'b0;

        byte_trans          = new('{8'h00, 8'h00});
        expected_crc        = 16'h1EA0;
        send_tx_data(byte_trans);

        byte_trans          = new('{8'h12, 8'h34});
        expected_crc        = 16'hCF26;
        send_tx_data(byte_trans);

        // 5) crc correct after sending random messages

        $display("Testing random Tx");
        check_rx_crc_ok     = 1'b0;
        check_tx_crc        = 1'b1;
        tx_append_crc       = 1'b1;
        check_crc_stable    = 1'b0;

        repeat (1000) begin
            byte_trans = ByteTransType::new_random_transaction($urandom_range(1, 10));

            expected_crc        = byte_trans.calculate_crc;
            send_tx_data(byte_trans);
            repeat (5) @(posedge clk) begin end
        end

        // 6) crc remains stable after sending, if:
        //  a) fdt_trigger doesn't fire
        //  b) tx_append_crc is not asserted at the time of fdt_trigger
        //  c) tx_iface.data_valid is not asserted at the time of fdt_trigger

        $display("Testing CRC remains stable during Tx if various conditions don't occur");

        // note: if we are in Tx mode then even if we don't trigger the start of a new CRC
        //       for any of the above reasons, we'll continue modifying the CRC when each
        //       tx data bit goes through. (except in case b). So enter rx mode here first

        // enter rx mode
        check_rx_crc_ok     = 1'b0;
        check_tx_crc        = 1'b0;
        byte_trans = ByteTransType::new_random_transaction(1);
        timeout             = 0;
        add_rx_data(byte_trans, timeout);
        rx_driver.wait_for_idle(timeout + 100);

        check_rx_crc_ok     = 1'b0;
        check_tx_crc        = 1'b0;
        tx_append_crc       = 1'b0;
        check_crc_stable    = 1'b1;

        // check case a) fdt_trigger doesn't fire
        // Note: the data sends because the sink doesn't wait for fdt trigger
        //       but the dut shouldn't calculate the CRC
        byte_trans = ByteTransType::new_random_transaction($urandom_range(0, 10));
        tx_append_crc       = 1'b1;         // tx_append_crc is 1
        send_tx_data(byte_trans,            // data_valid is 1
                     1'b0);                 // no fdt


        //  check case b) tx_append_crc is not asserted at the time of fdt_trigger
        tx_append_crc       = 1'b0;         // tx_append_crc is 0
        send_tx_data(byte_trans);           // data_valid is 1, fdt_trigger fires

        //  check case c) tx_iface.data_valid is not asserted at the time of fdt_trigger
        tx_append_crc       = 1'b1;         // tx_append_crc is 1
        @(posedge clk) begin end
        fdt_trigger         <= 1'b1;        // fdt trigger fires, but data_valid is low
        @(posedge clk) begin end
        fdt_trigger         <= 1'b0;
        send_tx_data(byte_trans,            // data gets sent but
                     1'b0);                 // fdt_trigger has already fired

        // stop checking the crc is stable now
        check_crc_stable    = 1'b0;

        // 7) Rx followed by Tx to emulate Rx + reply

        $display("Testing random Rx followed by Tx");
        check_rx_crc_ok     = 1'b1;
        expect_rx_crc_ok    = 1'b1;
        check_tx_crc        = 1'b1;
        tx_append_crc       = 1'b1;
        check_crc_stable    = 1'b0;

        repeat (1000) begin
            begin // rx block
                byte_trans = ByteTransType::new_random_transaction($urandom_range(0, 10));
                byte_trans.append_crc;
                timeout     = 0;
                add_rx_data(byte_trans, timeout);
                rx_driver.wait_for_idle(timeout + 100);
            end
            begin // tx block
                byte_trans      = ByteTransType::new_random_transaction($urandom_range(1, 10));
                expected_crc    = byte_trans.calculate_crc;

                send_tx_data(byte_trans);
            end
        end

        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

    // check rx_crc_ok as expected on EOC
    rxCrcOkAsExpected:
    assert property (
        @(posedge clk)
        ($rose(rx_iface.eoc) && check_rx_crc_ok) |-> (rx_crc_ok == expect_rx_crc_ok))
        else $error("rx_crc_ok (%b) not as expected", rx_crc_ok);

    // check rx_crc_ok stable from EOC until either the next SOC or fdt_trigger
    logic next_frame_start;
    assign next_frame_start = rx_iface.soc || fdt_trigger;
    rxCrcOkStable:
    assert property (
        @(posedge clk)
        $rose(rx_iface.eoc) |-> $stable(rx_crc_ok) throughout next_frame_start[->1])
        else $error("rx_crc_ok is not stable between frames");

    // check crc as expected after tx finishes
    txCrcOk:
    assert property (
        @(posedge clk)
        ($fell(tx_iface.data_valid) && check_tx_crc) |=>
            (crc == expected_crc))
        else $error("crc (%x) not as expected (%x) after tx", crc, expected_crc);

    // check crc stable from falling edge of tx_iface.data_valid until either the next SOC or fdt_trigger
    txCrcStable:
    assert property (
        @(posedge clk)
        $fell(tx_iface.data_valid) |=>  ##1 ($stable(crc) throughout next_frame_start[->1]))
        else $error("crc is not stable between frames");

    // check crc stable when check_crc_stable is asserted
    txCrcStable2:
    assert property (
        @(posedge clk)
        $rose(check_crc_stable) |=> $stable(crc) throughout !check_crc_stable[->1])
        else $error("crc is not stable when check_crc_stable is asserted");

    // assert that rx_crc_ok is asserted iff (crc == 0)
    rxCrcOkIffCrc0:
    assert property (
        @(posedge clk)
        (rx_crc_ok == (crc == 0)))
        else $error("rx_crc_ok (%b) doesn't match (crc (%x) == 0)", rx_crc_ok, crc);

endmodule
