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
    logic pcd_pause_n;  // not used, just here so that .* works
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

    always_ff @(posedge clk) begin
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
        //$display("Running test 1");
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
        wait(idle) begin end

        // 2) We also want to test the 4 combinations that have Y in the middle:
        //    X -> Y -> X
        //    X -> Y -> Z
        //    Z -> Y -> X
        //    Z -> Y -> Z
        //$display("Running test 2");
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
        wait(idle) begin end

        // 3) Generate a random queue of sequences (excludes error cases)
        //$display("Running test 3");
        seqs = bfm.generate_valid_sequence_queue(1000);
        expected = seqs;
        bfm.send_sequence_queue(seqs);
        wait(idle) begin end

        // 4) Test X -> Z error cases
        //$display("Running test 4");
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
        expected.push_back(PCDBitSequence_Y);
        expected.push_back(PCDBitSequence_Y);

        bfm.send_sequence_queue(seqs);
        wait(idle) begin end
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
            (idle && !seq_valid))
            else $error("signals invalid in reset");

    // check that we always produce a sequence on going idle
    // and that it is a Y.
    // The only exception is if we produced an PCDBitSequence_ERROR
    seqValidOnGoingIdle:
    assert property (
        @(posedge clk)
        disable iff (rst_for_asserts)
        ($rose(idle) && (seq != PCDBitSequence_ERROR)) |->
            ($rose(seq_valid) && seq == PCDBitSequence_Y))
        else $error("No valid sequence on DUT going idle");

    // check that after we go idle, there are no more expected sequences
    // Except if we produced an PCDBitSequence_ERROR
    // VCS doesn't like .size in an assert property
    always @(posedge clk) begin
        if ($rose(idle) && (seq != PCDBitSequence_ERROR)) begin
            noMoreExpectedAfterGoingIdle:
            assert (expected.size() == 0) else $error("DUT goes idle but more sequences expected");
        end
    end

    // ensure that the DUT goes none idle when the BFM is transmitting
    dutGoesNoneIdleDuringTransfer:
    assert property (
        @(posedge clk)
        disable iff (rst_for_asserts)
        $rose(sending) |=>
            (sending throughout !idle [->1]))    // sending stays true at least until idle goes to 0
        else $error("DUT fails to go none idle during transmission");

    // seqValid is only valid for one tick at a time
    seqValidOnlyOneTick:
    assert property (
        @(posedge clk)
        disable iff (rst_for_asserts)
        seq_valid |=> !seq_valid)
        else $error("seq_valid asserted for more than one tick");

endmodule
