/***********************************************************************
        File: iso14443_2a_tb.sv
 Description: A loopback based testbench for the iso14443_2a module
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

module iso14443_2a_tb;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic       clk;
    logic       rst_n;

    logic       pause_n_synchronised;

    rx_interface #(.BY_BYTE(0)) rx_iface(.*);
    tx_interface #(.BY_BYTE(0)) tx_iface(.*);

    logic       lm_out;

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    iso14443_2a dut (.*);

    // --------------------------------------------------------------
    // The source for the clock and pause_n signal
    // includes the pcd_pause_n driver
    // --------------------------------------------------------------
    analogue_sim analogue_sim_inst
    (
        .rst_n                  (rst_n),
        .picc_clk               (clk),
        .pcd_pause_n            (),
        .pause_n_async          (),
        .pause_n_synchronised   (pause_n_synchronised)
    );

    // our Rx send queue
    typedef pcd_pause_n_transaction_pkg::PCDPauseNTransaction RxSendTransType;
    RxSendTransType rx_send_queue [$];

    // --------------------------------------------------------------
    // The monitor for the rx_iface (output)
    // --------------------------------------------------------------

    rx_bit_iface_monitor_pkg::RxBitIfaceMonitor rx_monitor;

    // and the Rx recv_queue
    typedef rx_bit_transaction_pkg::RxMonitorBitTransaction RxRecvTransType;
    RxRecvTransType rx_recv_queue [$];

    // --------------------------------------------------------------
    // The source driver / queue for the tx_iface
    // --------------------------------------------------------------

    // driver
    tx_bit_iface_source_driver_pkg::TxBitIfaceSourceDriver tx_driver;

    // the send queue
    typedef tx_bit_transaction_pkg::TxBitTransaction TxTransType;
    TxTransType tx_send_queue[$];

    // --------------------------------------------------------------
    // The monitor for the load modulator
    // --------------------------------------------------------------

    // monitor
    load_modulator_monitor_pkg::LoadModulatorMonitor lm_monitor;

    // recv queue
    TxTransType tx_recv_queue   [$];

    // and what we expect to receive
    TxTransType tx_expected     [$];

    // interface
    load_modulator_iface lm_iface (.*);
    assign lm_iface.lm = lm_out;

    // --------------------------------------------------------------
    // The loopback
    // --------------------------------------------------------------
    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            tx_send_queue = '{};
        end
        else begin
            if (rx_recv_queue.size() != 0) begin
                automatic RxRecvTransType rx_trans = rx_recv_queue.pop_front();

                // drop error frames
                if (!rx_trans.error) begin
                    automatic TxTransType tx_trans = new(rx_trans.data);
                    tx_send_queue.push_back(tx_trans);
                end
            end
        end
    end

    // --------------------------------------------------------------
    // The verification stuff
    // --------------------------------------------------------------
    int check_count;

    always_ff @(posedge clk, negedge rst_n) begin: verificationBlock
        if (!rst_n) begin
            check_count = 0;
        end
        else begin: posedgeClk
            // wait for there to be an expected transaction and an actual transaction
            if ((tx_recv_queue.size() != 0) &&
                (tx_expected.size() != 0)) begin: readyToCompare
                // pop and compare
                automatic TxTransType received = tx_recv_queue.pop_front();
                automatic TxTransType expected = tx_expected.pop_front();

                dataAsExpected:
                assert (received.compare(expected)) else $error("Received %s, not as expected %p",
                        received.to_string, expected.to_string);

                check_count++;
                if ((check_count % 100) == 0) begin
                    $display("Received %d packets", check_count);
                end
            end
        end
    end

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin: testStimulus
        automatic int timeout;

        analogue_sim_inst.init();
        rx_monitor  = new(rx_iface);
        tx_driver   = new(tx_iface, 256, 256);  // 256 bits of idle after each tx (2 bit times)
        lm_monitor  = new(lm_iface);

        rx_send_queue   = '{};
        rx_recv_queue   = '{};
        tx_send_queue   = '{};
        tx_recv_queue   = '{};
        tx_expected     = '{};

        analogue_sim_inst.start(rx_send_queue);
        rx_monitor.start(rx_recv_queue);
        tx_driver.start(tx_send_queue);
        lm_monitor.start(tx_recv_queue);

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        timeout = 0;
        repeat(1000) begin: loops
            automatic RxRecvTransType   bit_trans;
            automatic RxSendTransType   pcd_trans;
            automatic TxTransType       expected;

            bit_trans = RxRecvTransType::new_random_transaction($urandom_range(1, 80), 1'b0);
            pcd_trans = new(bit_trans.convert_to_pcd_sequence_queue);
            expected = new(bit_trans.data);

            //$display("bit_trans: %s", bit_trans.to_string);
            //$display("pcd_trans: %s", pcd_trans.to_string);
            //$display("expected: %s", expected.to_string);

            timeout += analogue_sim_inst.driver.calculate_send_time(pcd_trans);

            rx_send_queue.push_back(pcd_trans);
            tx_expected.push_back(expected);
        end

        // wait for the PCD driver to be idle
        analogue_sim_inst.driver.wait_for_idle(timeout + 100);
        $display("rx_driver now idle (or timedout)");
        // wait for the rx_monitor to be idle
        rx_monitor.wait_for_idle(16, 32);
        $display("rx_monitor now idle (or timedout)");
        // wait for the tx_driver to be idle infinite timeout, because each send can time out
        tx_driver.wait_for_idle();
        $display("tx_driver now idle (or timedout)");
        // wait for the tx_monitor to be idle
        lm_monitor.wait_for_idle(64, 128);
        $display("lm_monitor now idle (or timedout)");

        // finally check that all the queues are empty
        queuesEmpty:
        assert ((rx_send_queue.size()   == 0) &&
                (rx_recv_queue.size()   == 0) &&
                (tx_send_queue.size()   == 0) &&
                (tx_recv_queue.size()   == 0) &&
                (tx_expected.size()     == 0))
            else $error("Not all queues are empty at end of test");

        repeat (5) @(posedge clk) begin end
        $stop;
    end


endmodule
