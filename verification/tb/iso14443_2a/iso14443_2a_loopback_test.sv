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
    // The source for the tx_iface
    // --------------------------------------------------------------

    tx_interface_source tx_source
    (
        .clk    (clk),
        .iface  (tx_iface)
    );

    // --------------------------------------------------------------
    // The sink for the rx_iface
    // --------------------------------------------------------------

    rx_interface_sink rx_sink
    (
        .clk    (clk),
        .iface  (rx_iface)
    );

    // --------------------------------------------------------------
    // The sink for the load modulator (tx_out)
    // --------------------------------------------------------------

    load_modulator_sink lm_sink (.*);

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin: testStimulus

        tx_source.initialise;
        rx_sink.initialise;
        lm_sink.initialise;

        rx_sink.enable_expected_checking(1'b0);
        rx_sink.enable_receive_queue(1'b1);

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

            // wait for it to be done and get the received data
            rx_sink.wait_for_idle(256);
            rq = rx_sink.get_and_clear_received_queue();

            // now send it out over the tx_iface
            tx_source.send_frame(rq);

            // wait for the load_modulator_sink to receive it all and then get the data
            lm_sink.wait_for_idle(0);
            rq = lm_sink.get_and_clear_received_queue();

            // received should have the SOC bit added (by the tx module) (1'b1)
            sq.push_front(1'b1);
            receivedAsExpected: assert(rq == sq)
                else $error("received not as expected, got %p expected %p", rq, sq);
        end

        repeat (5) @(posedge clk) begin end
        $stop;
    end


endmodule
