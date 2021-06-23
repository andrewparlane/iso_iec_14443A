/***********************************************************************
        File: pause_n_latch_and_synchroniser_tb.sv
 Description: Testbench for pause_n_latch_and_synchroniser
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

module pause_n_latch_and_synchroniser_tb;

    import ISO14443A_pkg::*;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic clk;
    logic rst_n;
    logic pause_n_async;
    logic pause_n_synchronised;

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    pause_n_latch_and_synchroniser dut (.*);

    // --------------------------------------------------------------
    // The source for the clock and pause_n signal
    // includes the pcd_pause_n driver
    // --------------------------------------------------------------
    analogue_sim analogue_sim_inst
    (
        .rst_n                  (rst_n),
        .picc_clk               (clk),
        .pcd_pause_n            (),
        .pause_n_async          (pause_n_async),
        .pause_n_synchronised   ()
    );

    // alias
    localparam int CLOCK_PERIOD_PS = analogue_sim_inst.clock_source_inst.CLOCK_PERIOD_PS;

    // our send queue
    typedef pcd_pause_n_transaction_pkg::PCDPauseNTransaction SendTransType;
    SendTransType send_queue [$];

    // --------------------------------------------------------------
    // Measure time between PICC clock edges (to check missing edges)
    // --------------------------------------------------------------
    longint async_deasserted_at = 64'd0;
    longint min_time_between_deasserts = 64'd1000000000;    // 1ms (all readings should be less than this)
    longint max_time_between_deasserts = 64'd0;

    always @(posedge pause_n_async) begin
        async_deasserted_at <= $time;
    end

    always @(posedge pause_n_synchronised) begin
        automatic longint deassert_delay = $time - async_deasserted_at;

        if (!rst_n) begin
            // this deassert is because we're in reset
            // ignore it
        end
        else begin
            if (deassert_delay < min_time_between_deasserts) begin
                min_time_between_deasserts <= deassert_delay;
            end
            if (deassert_delay > max_time_between_deasserts) begin
                max_time_between_deasserts <= deassert_delay;
            end
        end
    end

    // --------------------------------------------------------------
    // Helper functions / tasks
    // --------------------------------------------------------------

    // we don't really care what data we send here, just need a pause
    task send_data;
        static SendTransType trans = new('{PCDBitSequence_Z});

        // send it
        send_queue.push_back(trans);

        // wait for it to be done: 3 bit times @ 128 ticks each, plus a bit:
        //  PCDBitSequence_Z (SOC)      - 1 bit time
        //  idle time to enforce EOC    - 2 bit time
        analogue_sim_inst.driver.wait_for_idle(4*128 + 10);
    endtask

    function void randomise_params(logic stop_clock);
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

            // When simulating Fabricio's SPICE model I always saw the clock stoping before
            // the pause asserted. This may not be the case in the design when it's ported
            // to the new fabrication process, but it seems reasonable, and the closer this
            // simulation matches reality the better.
            // At the very least it must be < pcd_pause_len*CLOCK_PERIOD_PS, in order for the
            // clock_recovery model to work correctly.
            clock_stops_after_ps >= 0;
            clock_stops_after_ps < pause_n_asserts_after_ps;

            // Like pause_n_deasserts_after_ps, the only upper bound on the clock starting again
            // is that it should occur before the next pause starts. I constrain it to the same
            // range as pause_n_deasserts_after_ps (2us).
            clock_starts_after_ps >= 0;
            clock_starts_after_ps < 2*1000*1000;
            clock_starts_after_ps < (64 - pcd_pause_len - 3)*CLOCK_PERIOD_PS;

            // there's some simulation errors where we get the wrong number of ticks
            // if the clock/pause starts/stops exactly on an edge. So make sure that doesn't happen
            (clock_stops_after_ps*2 % CLOCK_PERIOD_PS) != 0;
            (clock_starts_after_ps*2 % CLOCK_PERIOD_PS) != 0;
            (pause_n_asserts_after_ps*2 % CLOCK_PERIOD_PS) != 0;
            (pause_n_deasserts_after_ps*2 % CLOCK_PERIOD_PS) != 0;
        };

        /* $display("\nUsing:");
        $display("  PCD pause length     %d ticks", pcd_pause_len);
        $display("  pause_n_asserts_after   %d ps", pause_n_asserts_after_ps);
        $display("  pause_n_deasserts_after %d ps", pause_n_deasserts_after_ps);
        $display("  clock_stops_after       %d ps", clock_stops_after_ps);
        $display("  clock_starts_after      %d ps", clock_starts_after_ps);
        $display("========================================"); */

        analogue_sim_inst.set_pause_ticks(pcd_pause_len);
        analogue_sim_inst.set_params(.clock_stops                   (stop_clock),
                                     .clock_stops_after_ps          (clock_stops_after_ps),
                                     .clock_starts_after_ps         (clock_starts_after_ps),
                                     .pause_n_asserts_after_ps      (pause_n_asserts_after_ps),
                                     .pause_n_deasserts_after_ps    (pause_n_deasserts_after_ps));
    endfunction

    // Constrain the parameters to our requirements for the AFE
    function void randomise_params_afe();
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

            // Pause Detector Requirements
            pause_n_asserts_after_ps >= 0;
            pause_n_asserts_after_ps < (pcd_pause_len*CLOCK_PERIOD_PS);
            pause_n_deasserts_after_ps >= 0;
            pause_n_deasserts_after_ps < 300*1000;  // 300ns

            // Clock recovery requirements
            clock_stops_after_ps >= 0;
            clock_stops_after_ps < (pcd_pause_len*CLOCK_PERIOD_PS);
            clock_starts_after_ps >= 0;
            clock_starts_after_ps < pause_n_deasserts_after_ps;

            // there's some simulation errors where we get the wrong number of ticks
            // if the clock/pause starts/stops exactly on an edge. So make sure that doesn't happen
            (clock_stops_after_ps*2 % CLOCK_PERIOD_PS) != 0;
            (clock_starts_after_ps*2 % CLOCK_PERIOD_PS) != 0;
            (pause_n_asserts_after_ps*2 % CLOCK_PERIOD_PS) != 0;
            (pause_n_deasserts_after_ps*2 % CLOCK_PERIOD_PS) != 0;
        };

        /* $display("\nUsing:");
        $display("  PCD pause length     %d ticks", pcd_pause_len);
        $display("  pause_n_asserts_after   %d ps", pause_n_asserts_after_ps);
        $display("  pause_n_deasserts_after %d ps", pause_n_deasserts_after_ps);
        $display("  clock_stops_after       %d ps", clock_stops_after_ps);
        $display("  clock_starts_after      %d ps", clock_starts_after_ps);
        $display("========================================"); */

        analogue_sim_inst.set_pause_ticks(pcd_pause_len);
        analogue_sim_inst.set_params(.clock_stops                   (1'b1),
                                     .clock_stops_after_ps          (clock_stops_after_ps),
                                     .clock_starts_after_ps         (clock_starts_after_ps),
                                     .pause_n_asserts_after_ps      (pause_n_asserts_after_ps),
                                     .pause_n_deasserts_after_ps    (pause_n_deasserts_after_ps));
    endfunction


    initial begin
        send_queue = '{};
        analogue_sim_inst.init();
        analogue_sim_inst.start(send_queue);

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // Test with the default values for the AFE
        // run two tests because the clock may start again with a falling edge or a rising edge
        $display("Testing with the default AFE values");
        min_time_between_deasserts = 64'd1000000000;
        max_time_between_deasserts = 64'd0;
        repeat(2) begin
            send_data;
        end

        $display("Time between pause_n_async deasserting and pause_n_synchronised deasserting:");
        $display("  min: %d", min_time_between_deasserts);
        $display("  max: %d", max_time_between_deasserts);
        $display("");
        repeat (5) @(posedge clk) begin end
        $stop;

        // test with the clock stopping (expected behaviour)
        $display("Testing with actual AFE requirements");
        min_time_between_deasserts = 64'd1000000000;
        max_time_between_deasserts = 64'd0;
        repeat (10000) begin
            randomise_params_afe;
            send_data;
        end

        $display("Time between pause_n_async deasserting and pause_n_synchronised deasserting:");
        $display("  min: %d", min_time_between_deasserts);
        $display("  max: %d", max_time_between_deasserts);
        $display("");

        $display("Testing with the clock stopping");
        min_time_between_deasserts = 64'd1000000000;
        max_time_between_deasserts = 64'd0;
        repeat (10000) begin
            randomise_params(1'b1);
            send_data;
        end

        $display("Time between pause_n_async deasserting and pause_n_synchronised deasserting:");
        $display("  min: %d", min_time_between_deasserts);
        $display("  max: %d", max_time_between_deasserts);
        $display("");

        // test with the clock not stopping.
        $display("Testing with the clock not stopping");
        min_time_between_deasserts = 64'd1000000000;
        max_time_between_deasserts = 64'd0;
        repeat (10000) begin
            randomise_params(1'b0);
            send_data;
        end

        $display("Time between pause_n_async deasserting and pause_n_synchronised deasserting:");
        $display("  min: %d", min_time_between_deasserts);
        $display("  max: %d", max_time_between_deasserts);
        $display("");

        repeat (5) @(posedge clk) begin end


        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

    // VCS doesn't like disable iff (!rst_n)
    logic rst;
    assign rst = !rst_n;

    in_reset:
    assert property (
        @(posedge clk)
        !rst_n |-> pause_n_synchronised)
        else $error("pause_n_synchronised asserted while in reset");

    // check that pause_n_synchronised asserts two ticks after pause_n_async
    assert_delay:
    assert property (
        @(posedge clk)
        disable iff (rst)
        $fell(pause_n_async) |->                // pause_n_async asserts, pause_n_latched asserts
                pause_n_synchronised[*2]        // pause_n_synchronised remains high on that tick and the next
            ##1 $fell(pause_n_synchronised))    // the tick after it should assert
        else $error("pausse_n_async -> pause_n_synchronised assertion timing issue");

    // check that pause_n_synchronised deasserts three ticks after pause_n_async
    // it's possible it won't even have asserted yet, so we can't check anything other
    // than it asserts 3 ticks later.
    deassert_delay:
    assert property (
        @(posedge clk)
        disable iff (rst)
        $rose(pause_n_async) |->
            ##3 $rose(pause_n_synchronised))
        else $error("pausse_n_async -> pause_n_synchronised deasserting timing issue");


endmodule
