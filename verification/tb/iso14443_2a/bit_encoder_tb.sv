/***********************************************************************
        File: bit_encoder_tb.sv
 Description: Testbench for bit_encoder
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
    // The source driver / queue for the in_iface
    // --------------------------------------------------------------

    // driver
    tx_bit_iface_source_driver_pkg::TxBitIfaceSourceDriver driver;

    // the send queue
    typedef tx_bit_transaction_pkg::TxBitTransaction TransType;
    TransType send_queue[$];

    // --------------------------------------------------------------
    // Clock generator
    // --------------------------------------------------------------

    clock_source clock_source_inst (.*);

    // --------------------------------------------------------------
    // Functions / Tasks
    // --------------------------------------------------------------
    // just use an expected queue here. This is the only test that looks at
    // the manchester encoded data, so there's no real need to have a full monitor
    logic expected [$];

    task send_data_verify_result (TransType trans);
        // set up the expected queue
        expected.delete;
        foreach (trans.data[i]) begin
            repeat (64) expected.push_back(trans.data[i]);
            repeat (64) expected.push_back(!trans.data[i]);
        end

        // sync to the clk
        @(posedge clk) begin end

        // prepare the data, and make sure it's ready to send
        send_queue.push_back(trans);
        repeat (4) @(posedge clk) begin end

        // set enable
        en <= 1'b1;

        // the driver finishes processing the transaction half way through the bit time
        // when req asserts and we have nothing left to send. However we have to wait
        // for the rest of that bit time to finish before disabling the DUT.
        // wait for the last_tick signal to assert
        driver.wait_for_idle(trans.data.size() * 128);
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
        automatic TransType trans = new();

        en <= 1'b0;

        driver      = new(in_iface, 8, 130);
        send_queue  = '{};
        driver.start(send_queue);

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // test just a single bit: 0
        trans.data = '{1'b0};
        send_data_verify_result(trans);
        repeat (5) @(posedge clk) begin end

        // test just a single bit: 1
        trans.data = '{1'b1};
        send_data_verify_result(trans);
        repeat (5) @(posedge clk) begin end

        // test two bits: 00
        trans.data = '{1'b0, 1'b0};
        send_data_verify_result(trans);
        repeat (5) @(posedge clk) begin end

        // test two bits: 10
        trans.data = '{1'b1, 1'b0};
        send_data_verify_result(trans);
        repeat (5) @(posedge clk) begin end

        // lots of tests of several bits
        repeat (1000) begin
            trans = TransType::new_random_transaction($urandom_range(1, 80));
            send_data_verify_result(trans);
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
