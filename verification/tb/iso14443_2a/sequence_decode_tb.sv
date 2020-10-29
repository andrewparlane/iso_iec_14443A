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
        .picc_clk               (clk),
        .pcd_pause_n            (),
        .pause_n_async          (),
        .pause_n_synchronised   (pause_n_synchronised)
    );

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

    initial begin
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
            analogue_sim_inst.set_bit_ticks(bit_len);
            for (int pause_len = 14; pause_len <= 50; pause_len++) begin
                $display("Testing with bit_len = %d, pause_len = %d", bit_len, pause_len);
                analogue_sim_inst.set_pause_ticks(pause_len);
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
