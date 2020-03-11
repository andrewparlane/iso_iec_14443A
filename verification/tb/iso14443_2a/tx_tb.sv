/***********************************************************************
        File: tx_tb.sv
 Description: Testbench for the tx module
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

module tx_tb;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic       clk;
    logic       rst_n;

    tx_interface #(.BY_BYTE(0)) in_iface(.*);

    // the Tx output signal is the manchester encoded data AND'ed with the subcarrier
    logic       tx_out;

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    tx dut (.*);

    // --------------------------------------------------------------
    // The source for the in_iface
    // --------------------------------------------------------------

    tx_interface_source tx_source
    (
        .clk    (clk),
        .iface  (in_iface)
    );

    // --------------------------------------------------------------
    // The sink for the load modulator (tx_out)
    // --------------------------------------------------------------

    load_modulator_sink lm_sink (.*);

    // --------------------------------------------------------------
    // Clock generator
    // --------------------------------------------------------------

    // Calculate our clock period in ps
    localparam CLOCK_FREQ_HZ = 13560000; // 13.56MHz
    localparam CLOCK_PERIOD_PS = 1000000000000.0 / CLOCK_FREQ_HZ;
    initial begin
        clk = 1'b0;
        forever begin
            #(int'(CLOCK_PERIOD_PS/2))
            clk = ~clk;
        end
    end

    // --------------------------------------------------------------
    // Functions / Tasks
    // --------------------------------------------------------------

    task send_data (logic sq[$]);
        automatic logic rq [$];
        //$display("sending %p", sq);

        // send it
        tx_source.send_frame(sq);
        lm_sink.wait_for_idle(512);

        // get the received data
        rq = lm_sink.get_and_clear_received_queue();

        // check we got what we sent + the SOC bit
        sq.push_front(1'b1);
        receivedAsExpected: assert(rq == sq)
            else $error("received not as expected, got %p expected %p", rq, sq);
    endtask

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin
        automatic logic sendQueue[$] = '{};

        tx_source.initialise;
        lm_sink.initialise;

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // Stuff to test
        //  0) SOC - done by add the SOC bit to expected queue
        //  1) nothing sends if data_valid is low
        in_iface.data_valid <= 1'b0;
        repeat (512) @(posedge clk) begin end
        // we'll error later if any data was received by the lm_sink

        //  2) correct number of bits are sent
        //      - implicity checked by adding all bits to the expected queue
        //        and by adding 2 bit times of idle to the end of the expected queue

        for (int i = 0; i < 100; i++) begin
            // add a random number of random bits to the sendQueue
            automatic int bits_to_send = $urandom_range(1, 100);
            $display("%d/100 - sending %d bits", i, bits_to_send);
            for (int i = 0; i < bits_to_send; i++) begin
                sendQueue.push_back(1'($urandom));
            end
            send_data(sendQueue);

            repeat (5) @(posedge clk) begin end
        end

        repeat (5) @(posedge clk) begin end
        $stop;
    end

endmodule
