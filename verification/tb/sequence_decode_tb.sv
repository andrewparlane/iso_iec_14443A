/***********************************************************************
        File: sequence_decode_tb.sv
 Description: Testbench for sequence_decode
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

module sequence_decode_tb;

    import ISO14443A_pkg::*;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic clk;
    logic rst_n;
    logic pause_n_synchronised;

    logic soc;
    logic eoc;
    logic data;
    logic data_valid;
    logic error;

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    sequence_decode dut (.*);

    // --------------------------------------------------------------
    // PICC -> PCD clock and comms generator
    // --------------------------------------------------------------
    logic pcd_pause_n;  // not used, just here so that .* works
    logic pause_n;
    logic sending;
    iso14443a_pcd_to_picc_comms_generator bfm (.*);

    // connect pause_n_synchronised and pause_n
    assign pause_n_synchronised = pause_n;

    // --------------------------------------------------------------
    // Verify sequence is as expected
    // --------------------------------------------------------------

    typedef struct packed
    {
        logic soc;
        logic eoc;
        logic data;
        logic data_valid;
        logic error;
    } Results;

    localparam Results EVENT_SOC    = '{1'b1, 1'b0, 1'bx, 1'b0, 1'b0};
    localparam Results EVENT_EOC    = '{1'b0, 1'b1, 1'bx, 1'b0, 1'b0};
    localparam Results EVENT_ERROR  = '{1'b0, 1'b0, 1'bx, 1'b0, 1'b1};
    localparam Results EVENT_DATA_0 = '{1'b0, 1'b0, 1'b0, 1'b1, 1'b0};
    localparam Results EVENT_DATA_1 = '{1'b0, 1'b0, 1'b1, 1'b1, 1'b0};

    Results outputs;
    assign outputs = '{soc, eoc, data, data_valid, error};

    Results expected[$];

    // has something happened this tick?
    logic event_detected;
    assign event_detected = soc | eoc | error | data_valid;

    always_ff @(posedge clk) begin
        if (event_detected) begin
            //$display("got event %p", outputs);

            eventDectedButNoneExpected:
                assert (expected.size != 0)
                else $error("event detected but not expecting anything: %p", outputs);

            if (expected.size != 0) begin: eventExpected
                automatic Results e = expected.pop_front;
                eventNotAsExpected:
                    assert (outputs ==? e) // ==? so we allow 'x in e as a wildcard
                    else $error("got event %p but expected %p", outputs, e);
            end
        end
    end

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    // helper task that runs multiple tests
    // so we can repeatedly use them with different settings
    task run_tests;
        automatic PCDBitSequence seqs[$] = '{};

        // 1) We have 10 sequences combinitions to check
        //    (ordered by when we test each)
        //    IDLE -> Z     - SOC
        //    Z    -> Z
        //    Z    -> X
        //    X    -> X
        //    X    -> Y
        //    Y    -> Z
        //    Y    -> X
        //    Y    -> Y     - EOC + IDLE
        //    Z    -> Y     - EOC
        //    X    -> Z     - INVALID (this is tested later
        //$display("Running test 1a");

        seqs = '{PCDBitSequence_Z,  // IDLE -> Z    SOC
                 PCDBitSequence_Z,  // Z    -> Z    0
                 PCDBitSequence_X,  // Z    -> X    1
                 PCDBitSequence_X,  // X    -> X    1
                 PCDBitSequence_Y,  // X    -> Y    0
                 PCDBitSequence_Z,  // Y    -> Z    0
                 PCDBitSequence_X,  //              1
                 PCDBitSequence_Y,  //              0
                 PCDBitSequence_X,  // Y    -> X    1
                 PCDBitSequence_Y,  //              EOC
                 PCDBitSequence_Y}; // Y    -> Y    EOC + IDLE

        expected = '{EVENT_SOC,
                     EVENT_DATA_0,
                     EVENT_DATA_1,
                     EVENT_DATA_1,
                     EVENT_DATA_0,
                     EVENT_DATA_0,
                     EVENT_DATA_1,
                     EVENT_DATA_0,
                     EVENT_DATA_1,
                     EVENT_EOC};

        bfm.send_sequence_queue(seqs);
        wait(expected.size == 0) begin end

        // Test Z -> Y EOC
        //$display("Running test 1b");
        seqs = '{PCDBitSequence_Z,  //          SOC
                 PCDBitSequence_X,  //          1
                 PCDBitSequence_Y,  //          0
                 PCDBitSequence_Z,  //          EOC
                 PCDBitSequence_Y,  // Z -> Y   EOC
                 PCDBitSequence_Y}; //          IDLE

        expected = '{EVENT_SOC,
                     EVENT_DATA_1,
                     EVENT_DATA_0,
                     EVENT_EOC};

        bfm.send_sequence_queue(seqs);
        wait(expected.size == 0) begin end

        // 2) Generate a bunch of random queue of sequences (excludes error cases)
        //$display("Running test 2");
        repeat (50) begin
            seqs = bfm.generate_valid_sequence_queue(100);
            expected = '{EVENT_SOC};
            // starts at 1 because [0] is SOC,
            // ends at size-3 because last two are YY
            for (int i = 1; i < seqs.size-2; i++) begin
                expected.push_back((seqs[i] == PCDBitSequence_X) ? EVENT_DATA_1 : EVENT_DATA_0);
            end
            if (seqs[$-2] == PCDBitSequence_Z) begin
                // ends in ZYY, which is EOC + IDLE
                void'(expected.pop_back);
            end
            expected.push_back(EVENT_EOC);

            // $display("sending: %p", seqs);
            // $display("expecting: %p", expected);

            bfm.send_sequence_queue(seqs);
            wait(expected.size == 0) begin end
        end

        // 3) Test X -> Z error cases
        //$display("Running test 3");
        seqs = '{PCDBitSequence_Z,  // SOC
                 PCDBitSequence_X,  // 1
                 PCDBitSequence_Z,  // error
                 PCDBitSequence_Z,  // ignored
                 PCDBitSequence_X,  // ignored
                 PCDBitSequence_Y,  // ignored
                 PCDBitSequence_X,  // ignored
                 PCDBitSequence_Y,  // EOC
                 PCDBitSequence_Y}; // EOC

        expected = '{EVENT_SOC,
                     EVENT_DATA_1,
                     EVENT_ERROR,
                     EVENT_EOC};

        bfm.send_sequence_queue(seqs);
        wait(expected.size == 0) begin end
    endtask


    initial begin
        //bfm.set_sequence_timings(4, 12, 6, 0);

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // Run the standard test suite with pause lengths between 14 and 50
        // We don't know what the actual pause length will be coming from the PCD
        // The spec defines mins and max timings, but it's a bit difficult to get
        // an actual minimum. I think it's possible to design a pause frame that
        // the PICC will only detect as being 6 cycles long. However that is unlikely.
        // Additionally the delays in detecting pause frames in the analogue core
        // are quite important in determining the effective pause frame length.
        // TODO: min pause_len is determined by pause_n_asserts_after
        //       we really need an idea of what values we should be using

        // We also test all bit length between 126 and 130 cycles.
        // I would be very suprised if this was ever not 128 cycles, but it's good to
        // check that this works even if it's slightly off for some reason.

        for (int bit_len = 126; bit_len <= 130; bit_len++) begin
            bfm.set_bit_length(bit_len);
            for (int pause_len = 14; pause_len <= 50; pause_len++) begin
                $display("Testing with bit_len = %d, pause_len = %d", bit_len, pause_len);
                bfm.set_pause_length(pause_len);
                run_tests;
            end
        end

        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

    // synopsys doesn't like "disable iff (!rst_n)"
    logic rst_for_asserts = !rst_n;

    // Check that the outputs are correct when in reset
    signalsInReset:
    assert property (
        @(posedge clk)
        !rst_n |->
            (!soc && !eoc && !data_valid && !error))
            else $error("signals invalid in reset");

    // soc is only asserted for one tick at a time
    socOnlyOneTick:
    assert property (
        @(posedge clk)
        soc |=> !soc)
        else $error("soc asserted for more than one tick");

    // eoc is only asserted for one tick at a time
    eocOnlyOneTick:
    assert property (
        @(posedge clk)
        eoc |=> !eoc)
        else $error("eoc asserted for more than one tick");

    // error is only asserted for one tick at a time
    errorOnlyOneTick:
    assert property (
        @(posedge clk)
        error |=> !error)
        else $error("error asserted for more than one tick");

    // data_valid is only asserted for one tick at a time
    dataValidOnlyOneTick:
    assert property (
        @(posedge clk)
        data_valid |=> !data_valid)
        else $error("data_valid asserted for more than one tick");

endmodule
