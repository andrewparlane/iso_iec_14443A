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

import ISO14443A_pkg::*;

module sequence_decode_tb;
    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic           clk;
    logic           rst_n;
    logic           pause_n_synchronised;

    PCDBitSequence  seq;
    logic           seq_valid;
    logic           idle;

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    sequence_decode dut (.*);

    // --------------------------------------------------------------
    // PICC -> PCD clock and comms generator
    // --------------------------------------------------------------
    logic pause_n;
    logic sending;
    iso14443a_pcd_to_picc_comms_generator bfm (.*);

    // connect pause_n_synchronised and pause_n
    // TODO: Is this valid? I think for testbenches there's no need for it to be synchronised
    //       plus we should run these same tests on the rx module where the pause_n signal
    //       is synchronised
    assign pause_n_synchronised = pause_n;

    // --------------------------------------------------------------
    // Verify sequence is as expected
    // --------------------------------------------------------------

    PCDBitSequence expected[$];

    always @(posedge clk) begin
        if (seq_valid) begin
            gotSeqValidButNotExpected:
                assert (expected.size != 0)
                else $error("seq_valid but not expecting anything");

            if (expected.size != 0) begin
                seqNotAsExpected:
                    assert (seq == expected[0])
                    else $error("got seq %s but expected %s", seq.name, expected[0].name);

                void'(expected.pop_front);
            end
        end
    end

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    // helper task that runs multiple tests
    // so we can repeatedly use them with different settings
    task run_tests;
        PCDBitSequence seqs[$];
        seqs.delete;    // apparently seqs is remembered over calls

        // 1) We have 9 sequences combinitions to check
        //    (ordered by when we test each)
        //    Z -> Z
        //    Z -> X
        //    X -> X
        //    X -> Y
        //    Y -> Z
        //    Z -> Y
        //    Y -> X
        //    Y -> Y    - IDLE
        //    X -> Z    - INVALID   // we test this later
        $display("Running test 1");
        seqs.push_back(PCDBitSequence_Z); // Start of Comms
        seqs.push_back(PCDBitSequence_Z); // Z -> Z
        seqs.push_back(PCDBitSequence_X); // Z -> X
        seqs.push_back(PCDBitSequence_X); // X -> X
        seqs.push_back(PCDBitSequence_Y); // X -> Y
        seqs.push_back(PCDBitSequence_Z); // Y -> Z
        seqs.push_back(PCDBitSequence_Y); // Z -> Y
        seqs.push_back(PCDBitSequence_X); // Y -> X
        seqs.push_back(PCDBitSequence_Y); // X -> Y - already tested but have to get back to Y to test idle
        seqs.push_back(PCDBitSequence_Y); // Y -> Y - IDLE
        expected = seqs;
        bfm.send_sequence_queue(seqs);
        wait(idle);

        // 2) We also want to test the 4 combinations that have Y in the middle:
        //    X -> Y -> X
        //    X -> Y -> Z
        //    Z -> Y -> X
        //    Z -> Y -> Z
        $display("Running test 2");
        seqs.delete;
        seqs.push_back(PCDBitSequence_Z);   // Start of comms
        seqs.push_back(PCDBitSequence_Y);   // Z -> Y -> Z
        seqs.push_back(PCDBitSequence_Z);
        seqs.push_back(PCDBitSequence_Y);   // Z -> Y -> X
        seqs.push_back(PCDBitSequence_X);
        seqs.push_back(PCDBitSequence_Y);   // X -> Y -> X
        seqs.push_back(PCDBitSequence_X);
        seqs.push_back(PCDBitSequence_Y);   // X -> Y -> Z
        seqs.push_back(PCDBitSequence_Z);

        seqs.push_back(PCDBitSequence_Y);   // go idle
        seqs.push_back(PCDBitSequence_Y);

        expected = seqs;
        bfm.send_sequence_queue(seqs);
        wait(idle);

        // 3) Generate a random queue of sequences (excludes error cases)
        $display("Running test 3");
        seqs = bfm.generate_valid_sequence_queue(10);
        expected = seqs;
        bfm.send_sequence_queue(seqs);
        wait(idle);

        // 4) Test X -> Z error cases
        $display("Running test 4");
        seqs.delete;
        seqs.push_back(PCDBitSequence_Z);   // Start of Comms
        seqs.push_back(PCDBitSequence_X);   // Z -> X
        seqs.push_back(PCDBitSequence_Z);   // X -> Z (error)
        seqs.push_back(PCDBitSequence_Z);   // misc
        seqs.push_back(PCDBitSequence_Y);   // idle part 1
        seqs.push_back(PCDBitSequence_Y);   // idle part 2

        expected.delete;
        expected.push_back(PCDBitSequence_Z);
        expected.push_back(PCDBitSequence_X);
        expected.push_back(PCDBitSequence_ERROR);

        bfm.send_sequence_queue(seqs);
        wait(idle);
    endtask


    initial begin
        //bfm.set_sequence_timings(4, 12, 6, 0);

        // reset for 5 ticks
        rst_n <= 0;
        repeat (5) @(posedge clk);
        rst_n <= 1;
        repeat (5) @(posedge clk);

        // Run the standard test suite several times with different settings

        // 1) defaults
        $display("Testing with default timings");
        run_tests;

        // 2) Max pause len
        $display("Testing with max pause len");
        bfm.set_pause_length(41);
        run_tests;

        // 3) Extra long pause len
        $display("Testing with extra long pause len");
        bfm.set_pause_length(50);
        run_tests;

        // 4) Short pause len
        // NOTE: This currently fails, since pause_n_asserts_after_ps
        //       is more than CLK_PERIOD * pause_len
        $display("Testing with short pause len");
        bfm.set_pause_length(14);
        run_tests;

        // 5) Min pause len according to ISO/IEC 14443-2
        // NOTE: This currently fails, since pause_n_asserts_after_ps
        //       is more than CLK_PERIOD * pause_len
        $display("Testing with min pause len");
        bfm.set_pause_length(6);
        run_tests;

        // TODO: loop this lots of time with varying timings:
        //          First just varying pause times, maybe do all of 4 - 45 ticks
        //          or just extremes and some in the middle
        //          Then random pause len in that range per bit
        //          Then we want to vary bit length by up to 2 each way
        //          Maybe make it constant per transaction at first then vary per bit?
        //          ...
        //          Then add a loop where we vary all timings randomly per bit and leave
        //          it to run for ages

        repeat (5) @(posedge clk);
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

    // Check that the outputs are correct when in reset
    signalsInReset:
    assert property (
        @(posedge clk)
        !rst_n |->
            (idle && !seq_valid));

    // check that we always produce a sequence on going idle
    // and that it is a Y.
    // The only exception is if we produced an PCDBitSequence_ERROR
    seqValidOnGoingIdle:
    assert property (
        @(posedge clk)
        disable iff (!rst_n)
        ($rose(idle) && (seq != PCDBitSequence_ERROR)) |->
            ($rose(seq_valid) && seq == PCDBitSequence_Y));

    // check that after we go idle, there are no more expected sequences
    // Except if we produced an PCDBitSequence_ERROR
    noMoreExpectedAfterGoingIdle:
    assert property (
        @(posedge clk)
        disable iff (!rst_n)
        ($rose(idle) && (seq != PCDBitSequence_ERROR)) |=>  // takes one tick to detect the seq_valid and pop it from the queue
            (expected.size == 0));

    // ensure that the DUT goes none idle when the BFM is transmitting
    dutGoesNoneIdleDuringTransfer:
    assert property (
        @(posedge clk)
        disable iff (!rst_n)
        $rose(sending) |=>
            (sending throughout !idle [->1]));   // sending stays true at least until idle goes to 0

    // seqValid is only valid for one tick at a time
    seqValidOnlyOneTick:
    assert property (
        @(posedge clk)
        disable iff (!rst_n)
        seq_valid |=> !seq_valid);

endmodule
