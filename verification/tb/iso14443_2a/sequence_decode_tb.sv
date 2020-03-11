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

    rx_interface #(.BY_BYTE(0)) out_iface (.*);

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    sequence_decode dut (.*);

    // --------------------------------------------------------------
    // The source for the clock and pause_n signal
    // --------------------------------------------------------------
    logic pcd_pause_n;  // not used, just here so that .* works
    logic pause_n;
    logic sending;
    pause_n_and_clock_source pause_n_source (.*);

    // connect pause_n_synchronised and pause_n
    assign pause_n_synchronised = pause_n;

    // --------------------------------------------------------------
    // The sink for the out_iface
    // --------------------------------------------------------------

    rx_interface_sink rx_sink
    (
        .clk    (clk),
        .iface  (out_iface)
    );

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

        rx_sink.clear_expected_queue;
        rx_sink.build_valid_frame_expected_queue('{1'b0, 1'b1, 1'b1, 1'b0, 1'b0, 1'b1, 1'b0, 1'b1});

        pause_n_source.send_sequence_queue(seqs);
        rx_sink.wait_for_expected_empty(seqs.size * 128 * 2);

        // Test Z -> Y EOC
        //$display("Running test 1b");
        seqs = '{PCDBitSequence_Z,  //          SOC
                 PCDBitSequence_X,  //          1
                 PCDBitSequence_Y,  //          0
                 PCDBitSequence_Z,  //          EOC
                 PCDBitSequence_Y,  // Z -> Y   EOC
                 PCDBitSequence_Y}; //          IDLE

        rx_sink.clear_expected_queue;
        rx_sink.build_valid_frame_expected_queue('{1'b1, 1'b0});

        pause_n_source.send_sequence_queue(seqs);
        rx_sink.wait_for_expected_empty(seqs.size * 128 * 2);

        // 2) Generate a bunch of random queue of sequences (excludes error cases)
        //$display("Running test 2");
        repeat (50) begin
            automatic logic bq[$];
            seqs = frame_generator_pkg::generate_valid_sequence_queue(100);

            // starts at 1 because [0] is SOC,
            // ends at size-3 because last two are YY
            for (int i = 1; i < seqs.size-2; i++) begin
                bq.push_back(seqs[i] == PCDBitSequence_X);
            end
            if (seqs[$-2] == PCDBitSequence_Z) begin
                // ends in ZYY, which is EOC + IDLE
                void'(bq.pop_back);
            end

            rx_sink.clear_expected_queue;
            rx_sink.build_valid_frame_expected_queue(bq);

            // $display("sending: %p", seqs);
            // $display("expecting: %p", expected);

            pause_n_source.send_sequence_queue(seqs);
            rx_sink.wait_for_expected_empty(seqs.size * 128 * 2);
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

        rx_sink.clear_expected_queue;
        rx_sink.add_expected_soc_event;
        rx_sink.add_expected_data_events('{1'b1});
        rx_sink.add_expected_error_event;
        rx_sink.add_expected_eoc_full_byte_event(1'b0);

        pause_n_source.send_sequence_queue(seqs);
        rx_sink.wait_for_expected_empty(seqs.size * 128 * 2);
    endtask


    initial begin
        //pause_n_source.set_sequence_timings(4, 12, 6, 0);

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
            pause_n_source.set_bit_length(bit_len);
            for (int pause_len = 14; pause_len <= 50; pause_len++) begin
                $display("Testing with bit_len = %d, pause_len = %d", bit_len, pause_len);
                pause_n_source.set_pause_length(pause_len);
                run_tests;
            end
        end

        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------
    // all asserts are in the sink and the rx_interface

endmodule
