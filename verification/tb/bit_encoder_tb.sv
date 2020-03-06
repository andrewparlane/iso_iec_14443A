/***********************************************************************
        File: bit_encoder_tb.sv
 Description: Testbench for bit_encoder
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

module bit_encoder_tb;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic clk;
    logic rst_n;
    logic en;
    logic encoded_data;
    logic last_tick;

    tx_interface #(.BY_BYTE(0)) in_iface(.*);

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    bit_encoder dut (.*);

    // --------------------------------------------------------------
    // The source for the in_iface
    // --------------------------------------------------------------

    tx_interface_source source
    (
        .clk    (clk),
        .iface  (in_iface)
    );

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
    logic expected [$];
    task send_data (logic bq[$]);
        // set up the expected queue
        expected.delete;
        foreach (bq[i]) begin
            repeat (64) expected.push_back(bq[i]);
            repeat (64) expected.push_back(!bq[i]);
        end

        // sync to the clk
        @(posedge clk) begin end

        // set enable and send the data
        en <= 1'b1;
        source.send_frame(bq);

        // wait for the last tick and sync to the clk edge
        wait (last_tick) begin end
        @(posedge clk) begin end

        // disable it
        en      <= 1'b0;

        // wait a few ticks
        repeat (5) @(posedge clk) begin end
        expectedEmpty:
        assert(expected.size() == 0) else $error("expected queue still contains bits");
    endtask

    // --------------------------------------------------------------
    // Verify data is as expected
    // --------------------------------------------------------------
    always_ff @(posedge clk) begin: expectedBlock
        if ($past(en)) begin: isEnabled
            automatic logic e = expected.pop_front;
            dataAsExpected:
            assert (encoded_data == e) else $error("Expected %b got %b", e, encoded_data);
        end
    end

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin
        en <= 1'b0;
        source.initialise;

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // test just a single bit: 0
        send_data('{1'b0});
        repeat (5) @(posedge clk) begin end

        // test just a single bit: 1
        send_data('{1'b1});
        repeat (5) @(posedge clk) begin end

        // test two bits: 00
        send_data('{1'b0, 1'b0});
        repeat (5) @(posedge clk) begin end

        // test two bits: 10
        send_data('{1'b1, 1'b0});
        repeat (5) @(posedge clk) begin end

        // lots of tests of several bits
        repeat (1000) begin
            automatic int num_bits = $urandom_range(1,10);
            automatic logic bq [$] = '{};
            repeat (num_bits) bq.push_back($urandom_range(1));
            send_data(bq);
            repeat (5) @(posedge clk) begin end
        end

        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

    inReset:
    assert property (
        @(posedge clk)
        !rst_n |-> (!in_iface.req && !last_tick))
        else $error("signals not as expecetd in reset");

    notEnabled:
    assert property (
        @(posedge clk)
        !en |=> (!in_iface.req && !last_tick && !$isunknown(encoded_data)))
        else $error("signals not as expecetd when not enabled");

    lastTickOneShot:
    assert property (
        @(posedge clk)
        $rose(last_tick) |=> $fell(last_tick))
        else $error("last_tick was asserted for more than one tick");

    // VCS doesn't like disable iff (!en)
    logic not_enabled;
    assign not_enabled = !en;

    bitPeriod1:
    assert property (
        @(posedge clk)
        disable iff (not_enabled)
        in_iface.req |=> (!in_iface.req[*127] ##1 in_iface.req))
        else $error("req doesn't pulse every 128 ticks");

    bitPeriod2:
    assert property (
        @(posedge clk)
        disable iff (not_enabled)
        last_tick |=> (!last_tick[*127] ##1 last_tick))
        else $error("last_tick doesn't pulse every 128 ticks");

    reqBeforeLastTick:
    assert property (
        @(posedge clk)
        $rose(en) |-> !last_tick throughout in_iface.req[->1])
        else $error("last_tick asserted before req");

endmodule
