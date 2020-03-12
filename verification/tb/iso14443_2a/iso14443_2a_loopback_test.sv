/***********************************************************************
        File: iso14443_2a_loopback_test.sv
 Description: a loopback test of the iso14443_2a module
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

module iso14443_2a_loopback_test;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic       clk;
    logic       rst_n;

    logic       pause_n_synchronised;

    rx_interface #(.BY_BYTE(0)) rx_iface(.*);
    tx_interface #(.BY_BYTE(0)) tx_iface(.*);

    logic       tx_out;

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    iso14443_2a dut (.*);

    // --------------------------------------------------------------
    // The source for the clock and pause_n signal
    // --------------------------------------------------------------
    logic sending;
    logic pcd_pause_n;
    logic pause_n;
    pause_n_and_clock_source pause_n_source (.*);

    // connect pause_n_synchronised and pause_n
    assign pause_n_synchronised = pause_n;

    // --------------------------------------------------------------
    // The sink for the load modulator (tx_out)
    // --------------------------------------------------------------

    load_modulator_sink lm_sink (.*);

    // --------------------------------------------------------------
    // Loopback
    // --------------------------------------------------------------

    // we ignore rx_iface.error, .soc and .eoc
    // we know they work as desired since we test them in other TBs

    logic loopbackQueue [$];

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            loopbackQueue.delete;
            tx_iface.data_valid <= 1'b0;
        end
        else begin
            if (rx_iface.data_valid) begin
                // rx has data
                if (!tx_iface.data_valid) begin
                    // first bit
                    // so just push it straight to the tx module inputs
                    tx_iface.data       <= rx_iface.data;
                    tx_iface.data_valid <= 1'b1;
                end
                else begin
                    // not the first byte, so push it to the queue
                    loopbackQueue.push_back(rx_iface.data);
                end
            end

            if (tx_iface.req) begin
                // tx wants more data
                if (loopbackQueue.size() == 0) begin
                    // no more data
                    tx_iface.data_valid <= 1'b0;
                end
                else begin
                    tx_iface.data       <= loopbackQueue.pop_front;
                    tx_iface.data_valid <= 1'b1;
                end
            end
        end
    end

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin: testStimulus

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        repeat(1000) begin: loops
            automatic int bits_to_send = $urandom_range(1, 80);
            automatic logic sq[$];
            automatic logic rq[$];

            // ISO14443-2A has no concept of parity bits or bytes or ... so just send a bit stream
            sq = frame_generator_pkg::generate_bit_queue(bits_to_send);
            pause_n_source.send_bit_queue_no_parity(sq);

            // wait for the load modulator sink to receive everything
            // since the clock stops during pauses each bit sent from the pause_n_source
            // takes ~96 ticks, however the return path takes 128 ticks per bit
            // so the tx gets further and further behind, so don't use a timeout here
            // just trust that it doesn't lock up. This isn't a problem in hardware, since
            // the FDT ensures Tx happens after Rx has finished
            lm_sink.wait_for_idle(0);
            rq = lm_sink.get_and_clear_received_queue();

            // received should have the SOC bit added (1'b1)
            sq.push_front(1'b1);
            receivedAsExpected: assert(rq == sq)
                else $error("received not as expected, got %p expected %p", rq, sq);
        end

        repeat (5) @(posedge clk) begin end
        $stop;
    end


endmodule
