/***********************************************************************
        File: loopback_test.sv
 Description: a loopback test to forward Rx data to Tx
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

module loopback_test;

    import ISO14443A_pkg::*;

    // --------------------------------------------------------------
    // Ports to Rx, Tx and FDT
    // --------------------------------------------------------------

    logic           clk;
    logic           rst_n;

    logic           pause_n_synchronised;

    logic           rx_soc;
    logic           rx_eoc;
    logic [7:0]     rx_data;
    logic [2:0]     rx_data_bits;
    logic           rx_data_valid;
    logic           rx_sequence_error;
    logic           rx_parity_error;
    logic           rx_last_bit;

    logic           fdt_trigger;

    logic [7:0]     tx_data;
    logic [2:0]     tx_data_bits;
    logic           tx_ready_to_send;
    logic           tx_req;
    logic           tx_out;

    // --------------------------------------------------------------
    // DUTs
    // --------------------------------------------------------------

    rx rx_inst
    (
        .clk                    (clk),
        .rst_n                  (rst_n),
        .pause_n_synchronised   (pause_n_synchronised),

        .soc                    (rx_soc),
        .eoc                    (rx_eoc),
        .data                   (rx_data),
        .data_bits              (rx_data_bits),
        .data_valid             (rx_data_valid),
        .sequence_error         (rx_sequence_error),
        .parity_error           (rx_parity_error),
        .last_bit               (rx_last_bit)
    );

    tx tx_inst
    (
        .clk                    (clk),
        .rst_n                  (rst_n),
        .fdt_trigger            (fdt_trigger),
        .data                   (tx_data),
        .data_bits              (tx_data_bits),
        .ready_to_send          (tx_ready_to_send),
        .req                    (tx_req),
        .tx                     (tx_out)
    );


    localparam real CLOCK_FREQ_HZ    = 13560000.0; //
    localparam real CLOCK_PERIOD_PS  = 1000000000000.0 / CLOCK_FREQ_HZ;

    // TODO: We should set these values based on the actual behaivour of the AFE
    //       and then run this testbench again
    //       don't forget to adjust the values in the pause_n_and_clock_source.
    //       also would need to add a delay to the tx_out signal to mimic output buffer
    //       + AFE delay on the transmit side

    // Based on simulation the rising edge of pause_n_synchronised occurs
    // 258,111ps after the rising edge of pcd_pause_n.
    localparam real PCD_PAUSE_N_TO_SYNCHRONISED_PS = 258111.0;

    // after fdt_trigger assert, the tx module sees it after 1 tick
    // the en signal is seen after another tick. So the data changes after 2 ticks
    localparam real TRIGGER_TO_MODULATION_EDGE_PS = CLOCK_PERIOD_PS * 2;

    localparam real IDEAL_TIMING_ADJUST = (PCD_PAUSE_N_TO_SYNCHRONISED_PS +
                                           TRIGGER_TO_MODULATION_EDGE_PS) / CLOCK_PERIOD_PS;

    // $rtoi() for truncation
    localparam int TIMING_ADJUST = $rtoi(IDEAL_TIMING_ADJUST);

    initial begin
        $display("Running loopback test with parameters:");
        $display("  PCD_PAUSE_N_TO_SYNCHRONISED_PS: %f", PCD_PAUSE_N_TO_SYNCHRONISED_PS);
        $display("  TRIGGER_TO_MODULATION_EDGE_PS: %f", TRIGGER_TO_MODULATION_EDGE_PS);
        $display("  Ideal TIMING_ADJUST: %f", IDEAL_TIMING_ADJUST);
        $display("  Actual TIMING_ADJUST: %d", TIMING_ADJUST);
    end

    fdt
    #(
        .TIMING_ADJUST  (TIMING_ADJUST)
    )
    fdt_inst
    (
        .clk                    (clk),
        .rst_n                  (rst_n),
        .pause_n_synchronised   (pause_n_synchronised),
        .last_rx_bit            (rx_last_bit),
        .trigger                (fdt_trigger)
    );

    // --------------------------------------------------------------
    // The source for the clock and pause_n signal
    // --------------------------------------------------------------
    logic pause_n_source_sending;
    logic pcd_pause_n;
    logic pause_n;
    pause_n_and_clock_source pause_n_source (.*);

    // connect pause_n_synchronised and pause_n
    assign pause_n_synchronised = pause_n;

    // --------------------------------------------------------------
    // Synchronise the pause_n signal
    // --------------------------------------------------------------
    // this is done in the top level module and passed to the rx and fdt
    // components for synthesis
    active_low_reset_synchroniser pause_n_synchroniser
    (
        .clk        (clk),
        .rst_n_in   (pause_n),
        .rst_n_out  (pause_n_synchronised)
    );

    // --------------------------------------------------------------
    // Loopback Rx to Tx
    // --------------------------------------------------------------

    logic [7:0] loopbackQueue [$];
    logic [2:0] lastByteBits;

    always @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            loopbackQueue.delete;
            tx_ready_to_send <= 1'b0;
        end
        else begin
            if (rx_data_valid) begin
                // rx has data
                if (!tx_ready_to_send) begin
                    // first byte
                    // so just push it straight to the tx module inputs
                    tx_data             <= rx_data;
                    tx_data_bits        <= rx_data_bits;
                    tx_ready_to_send    <= 1'b1;
                end
                else begin
                    // not the first byte, so push it to the queue
                    loopbackQueue.push_back(rx_data);

                    // this gets overwritten every byte we receive
                    // the Rx module only supports partial bytes on the last byte
                    // so all the rest are 8 bits
                    lastByteBits        <= rx_data_bits;
                end
            end

            if (tx_req) begin
                // tx wants more data
                if (loopbackQueue.size() == 0) begin
                    // no more data
                    tx_ready_to_send <= 1'b0;
                end
                else begin
                    tx_data             <= loopbackQueue.pop_front;
                    tx_ready_to_send    <= 1'b1;

                    if (loopbackQueue.size() == 0) begin
                        tx_data_bits        <= lastByteBits;
                    end
                    else begin
                        tx_data_bits        <= 3'd0; // 8 bits
                    end
                end
            end
        end
    end

    // --------------------------------------------------------------
    // Decode Tx data and verify it as being what we sent
    // --------------------------------------------------------------

    // Each bit time is 128 ticks, so we pass the tx_out through a 128 entry shift register
    // and compare it with the expected patterns for a logical 0,1 or idle
    logic [127:0] tx_out_shift_reg;

    always @(posedge clk) begin
        tx_out_shift_reg <= {tx_out_shift_reg[126:0], tx_out};
    end

    const logic [127:0] TX_PATTERN_0    = {64'b0, {4{8'hFF, 8'h00}}};
    const logic [127:0] TX_PATTERN_1    = {{4{8'hFF, 8'h00}}, 64'b0};
    const logic [127:0] TX_PATTERN_IDLE = {128'b0};

    logic expected [$];

    initial begin: txVerification
        forever begin: foreverTx
            // we know that Tx frames must start with SOC -> logic '1'
            // and a logic '1' is 64 1s followed by 64 0s.
            // Finally since the bit time must start with the subcarrier in the loaded
            // state. The first rising edge of the tx_out line is start of the bit time
            @(posedge tx_out) begin end
            @(posedge clk) begin end

            while (1) begin
                // wait for all of the bit time to be clocked in
                repeat(128) @(posedge clk) begin end

                if (tx_out_shift_reg == TX_PATTERN_IDLE) begin: dataIdle
                    // no data
                    notExpectingAnything:
                    assert (expected.size() == 0)
                        else $error("Tx is idle but was expecting data");

                    // clear the expected queue so that the wait in the test stimulas
                    // initial block will end
                    expected.delete;

                    // we've gone idle, wait for next SOC
                    break;
                end
                else begin: dataNotIdle
                    // got data
                    automatic logic actual = 1'bX;

                    if (tx_out_shift_reg == TX_PATTERN_0) begin
                        actual = 1'b0;
                    end
                    else if (tx_out_shift_reg == TX_PATTERN_1) begin
                        actual = 1'b1;
                    end

                    //$display("received %b", actual);

                    validPattern:
                    assert (!$isunknown(actual)) else $error("Invalid data received");

                    expectingSomething:
                    assert (expected.size())
                        else $error("Received data from the Tx module, but not expecting anything");

                    if (expected.size()) begin: somethingExpected
                        automatic logic e = expected.pop_front;

                        asExpected:
                        assert (e == actual) else $error("Got %b expecting %b", actual, e);
                    end
                end
            end
        end
    end

    // --------------------------------------------------------------
    // Check FDT timings
    // --------------------------------------------------------------

    // Timings, from ISO/IEC 14443-3:2016 section 6.2.1.1
    localparam real FDT_LAST_BIT_0 = 1172.0 * CLOCK_PERIOD_PS;
    localparam real FDT_LAST_BIT_1 = 1236.0 * CLOCK_PERIOD_PS;

    // this is a time in ps (`timescale)
    // note: we use pcd_pause_n here not pause_n or pause_n_synchronised
    //       as we want to meauser the times as seen by the PCD
    longint lastPauseRise;
    always_ff @(posedge pcd_pause_n) lastPauseRise <= $time;

    // note: we use tx_out here, as we don't yet support adding arbitrary delays
    //       between that and the load modulator activating.

    longint checkedForPauseAt;
    always_ff @(posedge tx_out) begin: triggerBlock
        if (lastPauseRise == checkedForPauseAt) begin
            // this is not the first rising edge of tx_out since the last pause
            // so we ignore it
        end
        else begin: firstEdge
            automatic longint fdt_measured = $time - lastPauseRise;
            automatic real earliest_allowed;
            automatic real latest_allowed;

            // first rising edge since the rising edge of the last pause (PCD side)
            checkedForPauseAt <= lastPauseRise;

            // the shortest time between the two edeges is the ideal time
            earliest_allowed = rx_last_bit ? FDT_LAST_BIT_1 : FDT_LAST_BIT_0;

            // and the longest time between the two edges is the ideal time + 0.4µs
            // but we impose tighter restrictions here and require it to be within 80ns
            latest_allowed = earliest_allowed + 80000.0;

            // NOTE: we use a timescale of ps, but 13.56MHz has a period of
            //       73746.312684365781710914454277286 ps, hence there is a small eror per
            //       tick. Over the range of 1236 ticks, that error is 386.5 ps
            //       which is ~0.5% of one tick, so we should be good here
            //$display("Measured FDT time must be between %f ps and %f ps, measured %d ps = %f ticks",
            //         earliest_allowed, latest_allowed, fdt_measured, (real'(fdt_measured) / CLOCK_PERIOD_PS));

            fdtTime:
            assert ((fdt_measured >= earliest_allowed) &&
                    (fdt_measured < latest_allowed))
                else $error("Measured FDT time must be between %f ps and %f ps, measured %d ps",
                            earliest_allowed, latest_allowed, fdt_measured);
        end
    end

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin: testStimulus
        automatic logic [7:0]   data[$];
        automatic logic         bits[$];

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        repeat(1000) begin
            automatic int bits_to_send          = $urandom_range(1, 80);
            automatic int bytes_to_send         = int'($ceil(bits_to_send / 8.0));
            automatic int bits_in_last_byte     = bits_to_send % 8;

            data = frame_generator_pkg::generate_byte_queue(bytes_to_send);
            bits = frame_generator_pkg::convert_message_to_bit_queue(data, bits_in_last_byte);
            bits = frame_generator_pkg::add_parity_to_bit_queue(bits);
            expected = '{1'b1}; // soc
            foreach (bits[i]) expected.push_back(bits[i]);

            // The Tx module always sends a parity after it has sent data_bits.
            // This is because the PICC only ever sends full byte comess to the PCD
            // (which always have parity bits) except for during AC frames.
            // In AC frames if the PCD sends the PICC 3 bits of the UID, the PICC responds
            // with the remaining 5 bits of that byte + the parity bit, and then the remaining
            // bytes as normal. Hence we always want to send a parity bit on PICC -> PCD comms
            // So we need to add the parity bit to the expected data queue manually, since
            // the frame_generator_pkg::add_parity_to_bit_queue only adds a parity bit after every 8 bits of data.
            if (bits_in_last_byte != 0) begin
                automatic logic parity = 1'b1;
                for (int i = 0; i < bits_in_last_byte; i++) begin
                    parity = parity ^ data[$][i];
                end
                expected.push_back(parity);
            end

            /* $display("sending %d bits = %d bytes + %d bits", bits_to_send, bytes_to_send, bits_in_last_byte);
            $display("data %p", data);
            $display("expected %p", expected); */

            pause_n_source.send_message_no_crc(data, bits_in_last_byte);

            wait (expected.size() == 0) begin end
            repeat (256) @(posedge clk) begin end
        end

        repeat (5) @(posedge clk) begin end
        $stop;
    end


endmodule
