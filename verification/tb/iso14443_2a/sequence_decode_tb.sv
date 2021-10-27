/***********************************************************************
        File: sequence_decode_tb.sv
 Description: Testbench for sequence_decode
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
    // includes the pcd_pause_n driver
    // --------------------------------------------------------------
    analogue_sim analogue_sim_inst
    (
        .rst_n                  (rst_n),
        .picc_clk               (clk),
        .pcd_pause_n            (),
        .pause_n_async          (),
        .pause_n_synchronised   (pause_n_synchronised)
    );

    // alias
    localparam int CLOCK_PERIOD_PS = analogue_sim_inst.clock_source_inst.CLOCK_PERIOD_PS;

    // our send queue
    typedef pcd_pause_n_transaction_pkg::PCDPauseNTransaction SendTransType;
    SendTransType send_queue [$];

    // --------------------------------------------------------------
    // The monitor for the out_iface
    // --------------------------------------------------------------

    rx_bit_iface_monitor_pkg::RxBitIfaceMonitor monitor;

    // and the recv_queue
    typedef rx_bit_transaction_pkg::RxMonitorBitTransaction RecvTransType;
    RecvTransType recv_queue [$];

    // --------------------------------------------------------------
    // Measure time between PICC clock edges (to check missing edges)
    // --------------------------------------------------------------
    longint last_picc_clock_edge = 64'd0;
    longint expected_missing_edges = 64'd0;

    always @(posedge clk, negedge clk) begin: missingEdgeChecking
        automatic longint now = $time;
        // skip the first edge
        if (last_picc_clock_edge != 0) begin: notZero
            automatic longint time_between_edges = now - last_picc_clock_edge;
            // ignore normal readings (when time between edges is period / 2
            // with a small margin for rounding errors
            if (time_between_edges > ((CLOCK_PERIOD_PS/2) + 64'd100)) begin: missingEdge
                // there were missing edges
                // the number of missing edges is:
                // (time_between_edges - CLOCK_PERIOD_PS/2)/CLOCK_PERIOD_PS/2
                longint missing_edges;
                missing_edges = (2*time_between_edges - CLOCK_PERIOD_PS)/CLOCK_PERIOD_PS;
                missingEdgeAssert:
                assert (missing_edges == expected_missing_edges)
                else $error("Missed %d edges expected %d", missing_edges, expected_missing_edges);
            end
        end
        last_picc_clock_edge <= now;
    end

    // --------------------------------------------------------------
    // Helper functions / tasks
    // --------------------------------------------------------------

    task send_data_verify_result(SendTransType trans, RecvTransType expected);
        automatic int timeout;

        timeout = analogue_sim_inst.driver.calculate_send_time(trans);

        // send it
        //$display("pushing trans: %p to queue", trans);
        send_queue.push_back(trans);

        // wait for it to be done
        analogue_sim_inst.driver.wait_for_idle(timeout + 256);
        monitor.wait_for_idle(256, 512);

        // verify
        receivedOneTransaction:
        assert (recv_queue.size() == 1) else $error("recv_queue.size() is %d, expecting 1", recv_queue.size());

        if (recv_queue.size() != 0) begin: recvQueueNotEmpty
            automatic RecvTransType recv = recv_queue.pop_front;
            receivedExpected:
            assert (recv.compare(expected)) else $error("Received %s, not as expected %p", recv.to_string, expected.to_string);
        end
    endtask

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    // helper task that runs multiple tests
    // so we can repeatedly use them with different settings
    task run_tests;
        automatic RecvTransType expected;
        automatic SendTransType trans;

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

        trans = new('{PCDBitSequence_Z,     // IDLE -> Z    SOC
                      PCDBitSequence_Z,     // Z    -> Z    0
                      PCDBitSequence_X,     // Z    -> X    1
                      PCDBitSequence_X,     // X    -> X    1
                      PCDBitSequence_Y,     // X    -> Y    0
                      PCDBitSequence_Z,     // Y    -> Z    0
                      PCDBitSequence_X,     //              1
                      PCDBitSequence_Y,     //              0
                      PCDBitSequence_X,     // Y    -> X    1
                      PCDBitSequence_Y,     //              EOC
                      PCDBitSequence_Y});   // Y    -> Y    EOC + IDLE

        expected = new('{1'b0, 1'b1, 1'b1, 1'b0, 1'b0, 1'b1, 1'b0, 1'b1}, 1'b0);
        send_data_verify_result(trans, expected);

        // Test Z -> Y EOC
        //$display("Running test 1b");
        trans = new('{PCDBitSequence_Z,     //          SOC
                      PCDBitSequence_X,     //          1
                      PCDBitSequence_Y,     //          0
                      PCDBitSequence_Z,     //          EOC
                      PCDBitSequence_Y,     // Z -> Y   EOC
                      PCDBitSequence_Y});   //          IDLE

        expected = new('{1'b1, 1'b0}, 1'b0);
        send_data_verify_result(trans, expected);

        // 2) Generate a bunch of random queue of sequences (excludes error cases)
        //$display("Running test 2");
        repeat (50) begin
            expected = RecvTransType::new_random_transaction($urandom_range(0, 100), 1'b0);
            trans = new(expected.convert_to_pcd_sequence_queue);
            send_data_verify_result(trans, expected);
        end

        // 3) Test X -> Z error cases
        //$display("Running test 3");
        trans = new('{PCDBitSequence_Z,     // SOC
                      PCDBitSequence_X,     // 1
                      PCDBitSequence_Z,     // error
                      PCDBitSequence_Z,     // ignored
                      PCDBitSequence_X,     // ignored
                      PCDBitSequence_Y,     // ignored
                      PCDBitSequence_X,     // ignored
                      PCDBitSequence_Y,     // EOC
                      PCDBitSequence_Y});   // EOC

        expected = new('{}, 1'b1);
        send_data_verify_result(trans, expected);
    endtask

    task assign_vars_and_test(int missing_edges,
                              int pcd_pause_len,
                              int pause_n_asserts_after_ps,
                              int pause_n_deasserts_after_ps,
                              int clock_stops_after_ps,
                              int clock_starts_after_ps);
        $display("\nUsing:");
        $display("  missing edges        %d edges", missing_edges);
        $display("  PCD pause length     %d ticks", pcd_pause_len);
        $display("  pause_n_asserts_after   %d ps", pause_n_asserts_after_ps);
        $display("  pause_n_deasserts_after %d ps", pause_n_deasserts_after_ps);
        $display("  clock_stops_after       %d ps", clock_stops_after_ps);
        $display("  clock_starts_after      %d ps", clock_starts_after_ps);
        $display("========================================");

        analogue_sim_inst.set_pause_ticks(pcd_pause_len);
        analogue_sim_inst.set_params(.clock_stops                   (missing_edges != 0),
                                     .clock_stops_after_ps          (clock_stops_after_ps),
                                     .clock_starts_after_ps         (clock_starts_after_ps),
                                     .pause_n_asserts_after_ps      (pause_n_asserts_after_ps),
                                     .pause_n_deasserts_after_ps    (pause_n_deasserts_after_ps));

        expected_missing_edges = 64'(missing_edges);

        run_tests;
    endtask

    task randomise_vars_and_test(int missing_edges);
        int pcd_pause_len;
        int pause_n_asserts_after_ps;
        int pause_n_deasserts_after_ps;
        int clock_stops_after_ps;
        int clock_starts_after_ps;

        std::randomize(pcd_pause_len,
                       pause_n_asserts_after_ps, pause_n_deasserts_after_ps,
                       clock_stops_after_ps, clock_starts_after_ps)
        with
        {
            // ISO/IEC 14443-2A:2016 section 8.1.2.1
            // figure 3 and table 4. PCD pause length is T1. The time from when it starts
            // transmitting a pause until it starts stopping to transmit a pause.
            // My DUT shouldn't care about this length though, so I've increased the tested
            // range. This gives more flexibility to the other parameters, ensuring we test
            // larger ranges of those.
            pcd_pause_len >= 10;
            pcd_pause_len <= 50;

            // The AFE must detect the pause before the PCD finishes transmitting it.
            // Otherwise the amplitude of the carrier wave will start to rise and the AFE
            // may not detect the pause at all.
            // This constraint is also required for my pause_detect model to work correctly.
            pause_n_asserts_after_ps >= 0;
            pause_n_asserts_after_ps < (pcd_pause_len*CLOCK_PERIOD_PS);

            // The upper bound on this is that the end of the pause has to come before the
            // start of the pause of the next sequence. Which means at most 64 - pcd_pause_len
            // ticks (for an X->Z (error)). Minus up to 3 ticks more for the synchroniser.
            // However that would be pretty extreme if pcd_pause_len were on the lower end
            // (64 - 10 - 3 = 51). When simulating Fabricio's SPICE model the largest delay I
            // found here was ~600ns which is just over 8 ticks. I'm using 2us here as an
            // upper bound, which is about 27 ticks, that's plenty of flexibility.
            pause_n_deasserts_after_ps >= 0;
            pause_n_deasserts_after_ps < 2*1000*1000;
            pause_n_deasserts_after_ps < (64 - pcd_pause_len - 3)*CLOCK_PERIOD_PS;

            // If the clock is going to stop during a pause, it must stop before the PCD finishes
            // transmitting the pause.
            clock_stops_after_ps >= 0;
            clock_stops_after_ps < (pcd_pause_len*CLOCK_PERIOD_PS);

            // Like pause_n_deasserts_after_ps, the only upper bound on the clock starting again
            // is that it should occur before the next pause starts. I constrain it to the same
            // range as pause_n_deasserts_after_ps (2us).
            clock_starts_after_ps >= 0;
            clock_starts_after_ps < 2*1000*1000;
            clock_starts_after_ps < (64 - pcd_pause_len - 3)*CLOCK_PERIOD_PS;

            // when the PICC clock stops we miss a certain number of edges compared to the
            // PCD clock. We want that number to be missing_edges. If the clocks stopped at the
            // very start of the pause and started again at the very end of the pause, the number
            // of missing edges would be pcd_pause_len*2 (two edges per tick).
            // If you increase clock_stops_after_ps then you reduce the number of missing edges.
            // If you increase clock_starts_after_ps then you increase the number of missing edges.
            // So missing_edges = 2*pcd_pause_len -
            //                    $floor(2.0*clock_stops_after_ps/CLOCK_PERIOD_PS) +
            //                    $floor(2.0*clock_starts_after_ps/CLOCK_PERIOD_PS)
            //
            // we want to pick values such that missing_edges is as desired
            // VCS doesn't support reals in the constraint block, meaning we can't do
            // $floor(2.0*...). Normally when casting from a real to an int SV rounds to nearest
            // whereas we want to truncate. However since all values are ints the resullt of the
            // division is automatically truncated, we confirm we miss the correct number of edges
            // by measuring the time between clock edeges above.
            //
            // If missing_edges is 0, then the clock doesn't stop, and we can ignore this constraint
            (missing_edges == 0) ||
            (missing_edges == (2*pcd_pause_len) -
                              ((2*clock_stops_after_ps)/CLOCK_PERIOD_PS) +
                              ((2*clock_starts_after_ps)/CLOCK_PERIOD_PS));

            // there's some errors where we get the wrong number of ticks if the clock starts
            // or stops exactly on an edge. So make sure that doesn't happen
            (clock_stops_after_ps*2 % CLOCK_PERIOD_PS) != 0;
            (clock_starts_after_ps*2 % CLOCK_PERIOD_PS) != 0;
        };

        assign_vars_and_test(.missing_edges                 (missing_edges),
                             .pcd_pause_len                 (pcd_pause_len),
                             .pause_n_asserts_after_ps      (pause_n_asserts_after_ps),
                             .pause_n_deasserts_after_ps    (pause_n_deasserts_after_ps),
                             .clock_stops_after_ps          (clock_stops_after_ps),
                             .clock_starts_after_ps         (clock_starts_after_ps));
    endtask

    initial begin
        int missing_edges;
        analogue_sim_inst.init();
        monitor = new (out_iface);

        send_queue = '{};
        recv_queue = '{};

        analogue_sim_inst.start(send_queue);
        monitor.start(recv_queue);

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // for debugging
        /* assign_vars_and_test(.missing_edges                 (115),
                             .pcd_pause_len                 (50),
                             .pause_n_asserts_after_ps      (3325529),
                             .pause_n_deasserts_after_ps    (959786),
                             .clock_stops_after_ps          (146774),
                             .clock_starts_after_ps         (676579));
        repeat (5) @(posedge clk) begin end
        $stop; */

        // AFE must drop at most 59 ticks (118) edges.
        // In this range my tests always pass, out of this range they can fail.
        // 100 loops of randomise_vars_and_test takes ~2 minutes. I don't think theer's much point
        // in testing every possible value for missing_edges, I'm more interested
        // in running lots of test for each missing_edges, varying the other parameters
        // We test the lower end, the upper end and then a bunch of random ones in the middle.

        // missed_ticks: 0 - 3, lower range
        for (int missing_edges = 0; missing_edges <= 3; missing_edges++) begin
            repeat (100) begin
                randomise_vars_and_test(missing_edges);
            end
        end

        // missed_ticks: 115 - 116, first half of upper range
        for (int missing_edges = 115; missing_edges <= 116; missing_edges++) begin
            repeat (100) begin
                randomise_vars_and_test(missing_edges);
            end
        end

        // missed_ticks: 117 - 118, second half of upper range
        // These can only be run if the dataValidOnlyOneTick assert in the rx_interface is disabled
        // That's because when detecting: XYZ, with certain timings the timeout detects the Y on one
        // tick, and the end of the next pause on the next tick, leading to data_valid being asserted
        // for two ticks in a row. This isn't a problem, that assert only exists to make sure we don't
        // accidentally leave the data_valid signal asserted normally.
        $assertoff(0, out_iface.useAsserts.dataValidOnlyOneTick);
        for (int missing_edges = 117; missing_edges <= 118; missing_edges++) begin
            repeat (100) begin
                randomise_vars_and_test(missing_edges);
            end
        end
        $asserton(0, out_iface.useAsserts.dataValidOnlyOneTick);

        // missed_ticks: random selection from 4 - 114 (middle)
        repeat (1000) begin
            randomise_vars_and_test($urandom_range(4,114));
        end

        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------
    // all asserts are in the sink and the rx_interface

endmodule
