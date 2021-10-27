/***********************************************************************
        File: tx_tb.sv
 Description: Testbench for the tx module
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

module tx_tb;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic       clk;
    logic       rst_n;

    tx_interface #(.BY_BYTE(0)) in_iface(.*);

    // the lm_out signal is the manchester encoded data AND'ed with the subcarrier
    // which is sent to the load modulator
    logic       lm_out;

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    tx dut (.*);

    // --------------------------------------------------------------
    // The source driver / queue for the in_iface
    // --------------------------------------------------------------

    // driver
    tx_bit_iface_source_driver_pkg::TxBitIfaceSourceDriver driver;

    // the send queue
    typedef tx_bit_transaction_pkg::TxBitTransaction TransType;
    TransType send_queue[$];

    // --------------------------------------------------------------
    // The monitor for the load modulator (lm_out)
    // --------------------------------------------------------------

    // monitor
    load_modulator_monitor_pkg::LoadModulatorMonitor monitor;

    // recv queue
    TransType recv_queue[$];

    // interface
    load_modulator_iface lm_iface (.*);
    assign lm_iface.lm = lm_out;

    // --------------------------------------------------------------
    // Clock generator
    // --------------------------------------------------------------

    clock_source clock_source_inst (.*);

    // --------------------------------------------------------------
    // Functions / Tasks
    // --------------------------------------------------------------

    task send_data_verify_result(TransType trans);
        // send it
        send_queue.push_back(trans);

        // wait for the monitor to be idle
        // wait for 16 ticks of idle in a row - this lets the driver get started
        // each bit takes 128 ticks to send, and we have 1 bit of idle and 1 bit of SOC
        // on top of the data bits, then +2 extra just to be sure.
        monitor.wait_for_idle(16, ((trans.data.size() + 4) * 128));

        // verify
        receivedOneTransaction:
        assert (recv_queue.size() == 1) else $error("recv_queue.size() is %d, expecting 1", recv_queue.size());

        if (recv_queue.size() != 0) begin: recvQueueNotEmpty
            automatic TransType recv = recv_queue.pop_front;
            receivedExpected:
            assert (recv.compare(trans)) else $error("Received %s, not as expected %p", recv.to_string, trans.to_string);
        end
    endtask

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin: testStimulus
        automatic logic sendQueue[$] = '{};

        driver  = new(in_iface, 8, 256);
        monitor = new(lm_iface);

        send_queue = '{};
        recv_queue = '{};

        driver.start(send_queue);
        monitor.start(recv_queue);

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // Stuff to test
        //  0) SOC - done in the monitor by checking for a '1' and not adding it to the transaction
        //  1) nothing sends if data_valid is low (done by the driver)
        repeat (512) @(posedge clk) begin end
        nothingSentWhenDataValidLow:
        assert (monitor.idle && (recv_queue.size() == 0))
            else $error("With data_valid low, the monitor is either not idle (%b) or has received some frames %d",
                        monitor.idle, recv_queue.size());

        //  2) correct data is set
        for (int j = 1; j <= 100; j++) begin
            // create a transaction of a random number of random bits
            automatic TransType trans = TransType::new_random_transaction($urandom_range(1, 100));

            $display("%d/100 - sending %d bits", j, trans.data.size);

            send_data_verify_result(trans);

            repeat (5) @(posedge clk) begin end
        end

        repeat (5) @(posedge clk) begin end
        $stop;
    end

endmodule
