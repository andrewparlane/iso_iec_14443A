/***********************************************************************
        File: framing_tb.sv
 Description: Testbench for framing
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

module framing_tb;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic           clk;
    logic           rst_n;

    logic           pause_n_synchronised;

    rx_interface #(.BY_BYTE(0)) in_rx_iface (.*);
    rx_interface #(.BY_BYTE(0)) out_rx_iface_bits (.*);
    rx_interface #(.BY_BYTE(1)) out_rx_iface_bytes (.*);

    logic           rx_crc_ok;

    tx_interface #(.BY_BYTE(1)) in_tx_iface (.*);
    logic           tx_append_crc;

    tx_interface #(.BY_BYTE(0)) out_tx_iface (.*);

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    localparam TIMING_ADJUST = 1100;    // 1100 to speed up the simulation

    framing
    #(
        .FDT_TIMING_ADJUST(TIMING_ADJUST)
    )
    dut (.*);

    // --------------------------------------------------------------
    // Clock generator
    // --------------------------------------------------------------

    // Calculate our clock period in ps
    // Using 10MHz clock, so we can work with an integer period
    // avoiding timing errors generated due to the simulator only having ps accuracy
    // note: this won't be an issue in synthesis
    localparam real CLOCK_FREQ_HZ    = 10000000.0; // 10MHz
    localparam real CLOCK_PERIOD_PS = 1000000000000.0 / CLOCK_FREQ_HZ;
    initial begin
        clk = 1'b0;
        forever begin
            #(int'(CLOCK_PERIOD_PS/2))
            clk = ~clk;
        end
    end

    // --------------------------------------------------------------
    // The source for the in_rx_iface
    // --------------------------------------------------------------

    rx_interface_source rx_source
    (
        .clk    (clk),
        .iface  (in_rx_iface)
    );

    // --------------------------------------------------------------
    // The sink for the out_rx_iface_bits
    // --------------------------------------------------------------

    rx_interface_sink rx_sink_bits
    (
        .clk    (clk),
        .iface  (out_rx_iface_bits)
    );

    // --------------------------------------------------------------
    // The sink for the out_rx_iface_bytes
    // --------------------------------------------------------------

    rx_interface_sink rx_sink_bytes
    (
        .clk    (clk),
        .iface  (out_rx_iface_bytes)
    );

    // --------------------------------------------------------------
    // The source for the in_tx_iface
    // --------------------------------------------------------------

    tx_interface_source tx_source
    (
        .clk    (clk),
        .iface  (in_tx_iface)
    );

    // --------------------------------------------------------------
    // The sink for the out_tx_iface
    // --------------------------------------------------------------

    tx_interface_sink tx_sink
    (
        .clk    (clk),
        .iface  (out_tx_iface)
    );

    // --------------------------------------------------------------
    // FDT verification
    // --------------------------------------------------------------

    // Timings, from ISO/IEC 14443-3:2016 section 6.2.1.1
    localparam int FDT_LAST_BIT_0 = 1172 - TIMING_ADJUST;
    localparam int FDT_LAST_BIT_1 = 1236 - TIMING_ADJUST;

    // measure the time between the rising edge of pause_n_synchronised
    // and the rising edge of data_valid

    // this is a time in ps (`timescale)
    longint lastPauseRise;
    always_ff @(posedge pause_n_synchronised) lastPauseRise <= $time;

    logic last_rx_bit;
    always_ff @(posedge out_tx_iface.data_valid) begin: triggerBlock
        // tx has started
        automatic longint diff = $time - lastPauseRise;
        automatic longint expected = CLOCK_PERIOD_PS * (last_rx_bit ? FDT_LAST_BIT_1 : FDT_LAST_BIT_0);
        //$display("Tx started at %d ps, lastPauseRise %d ps, diff %d ps (%d ticks), expected %d ps (%d ticks)",
        //         $time, lastPauseRise, diff, int'(diff / CLOCK_PERIOD_PS), expected, int'(expected / CLOCK_PERIOD_PS));

        fdtTime: assert (diff == expected)
            else $error("Tx started at %d ps, lastPauseRise %d ps, diff %d, expected %d",
                        $time, lastPauseRise, diff, expected);
    end

    // --------------------------------------------------------------
    // Tasks and functions
    // --------------------------------------------------------------
    logic check_rx_crc_ok;
    logic expect_rx_crc_ok;

    task send_rx_frame (int num_bits, logic corrupt_data=1'b0);
        automatic int           num_bytes           = int'($ceil(num_bits / 8.0));
        automatic int           bits_in_last_byte   = num_bits % 8;
        automatic logic [7:0]   data [$];
        automatic logic         bits [$];

        // only check rx_crc_ok if we add the CRC to the data
        check_rx_crc_ok = 1'b0;

        // generate the data
        data = frame_generator_pkg::generate_byte_queue(num_bytes);

        // add the CRC
        if (bits_in_last_byte == 0) begin
            // add the CRC if sending a whole number of bytes
            data                = frame_generator_pkg::add_crc_to_message(data);
            check_rx_crc_ok     = 1'b1;
            expect_rx_crc_ok    = 1'b1;
        end

        // corrupt the data?
        if (corrupt_data) begin
            automatic int byte_idx  = $urandom_range(0,num_bytes+1);
            automatic int bit_idx   = $urandom_range(0,7);
            data[byte_idx][bit_idx] = !data[byte_idx][bit_idx];
            expect_rx_crc_ok        = 1'b0;
        end

        bits = frame_generator_pkg::convert_message_to_bit_queue_for_rx(data, bits_in_last_byte);

        // set up the expected queues
        rx_sink_bits.build_valid_frame_expected_queue(bits);
        rx_sink_bytes.build_valid_frame_expected_queue(data, bits_in_last_byte);

        //$display("sending data: %p", data);
        //$display("bits: %p", bits);
        //$display("bits + parity: %p", frame_generator_pkg::add_parity_to_bit_queue(bits));

        // send the bits with the parity bits added
        bits = frame_generator_pkg::add_parity_to_bit_queue(bits);
        last_rx_bit = bits[$];
        rx_source.send_frame(bits);

        // wait until we're done
        rx_sink_bits.wait_for_expected_empty(16);
        rx_sink_bytes.wait_for_expected_empty(16);

        // wait a couple of clock ticks
        repeat (20) @(posedge clk) begin end
    endtask

    // note: we'll never add the crc if num_bits is not a whole byte
    task send_tx_frame (int num_bits, logic add_crc);
        automatic int           num_bytes           = int'($ceil(num_bits / 8.0));
        automatic int           bits_in_first_byte  = num_bits % 8;
        automatic logic [7:0]   data            [$];
        automatic logic [7:0]   expected_data   [$];
        automatic logic         expected_bits   [$];

        // generate the data
        data = frame_generator_pkg::generate_byte_queue(num_bytes);

        // generate expected queue
        // we expect the data + CRC with parity bits
        // the crc only gets added if add_crc and bits_in_first_byte == 0
        if ((bits_in_first_byte == 0) && add_crc) begin
            tx_append_crc <= 1'b1;
            expected_data = frame_generator_pkg::add_crc_to_message(data);
        end
        else begin
            tx_append_crc <= 1'b0;
            expected_data = data;
        end
        expected_bits = frame_generator_pkg::convert_message_to_bit_queue_for_tx(expected_data, bits_in_first_byte);
        expected_bits = frame_generator_pkg::add_parity_to_bit_queue(expected_bits, bits_in_first_byte);
        tx_sink.set_expected_queue(expected_bits);

        // The frame_encoder will never send until it gets the FDT trigger
        // which means we have to set the FDT timer running by pulsing pause_n_synchronised
        pause_n_synchronised <= 1'b0;
        @(posedge clk) begin end
        pause_n_synchronised <= 1'b1;

        // $display("sending data %p, bits_in_first_byte %d, adding crc %b (%x)",
        //          data, bits_in_first_byte, tx_append_crc, frame_generator_pkg::calculate_crc(data));
        // $display("expected %p", expected_bits);

        // send it
        tx_source.send_frame(data, bits_in_first_byte);

        // wait for the sink to have received it
        tx_sink.wait_for_expected_empty(512);

        // wait a couple of clock ticks
        repeat (20) @(posedge clk) begin end
    endtask

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin

        rx_source.initialise;
        rx_sink_bits.initialise;
        rx_sink_bytes.initialise;
        tx_source.initialise;
        tx_sink.initialise;

        pause_n_synchronised    = 1'b1;
        tx_append_crc           = 1'b0;

        /* rx_sink_bits.enable_expected_checking(1'b0);
        rx_sink_bytes.enable_expected_checking(1'b0);
        rx_sink_bits.enable_receive_queue(1'b1);
        rx_sink_bytes.enable_receive_queue(1'b1); */

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // 1) rx + CRC
        $display("Testing Rx + CRC");
        repeat (1000) send_rx_frame($urandom_range(1, 10) * 8);
        // 2) rx ending in partial byte (no CRC)
        $display("Testing Rx ending with partial bytes");
        repeat (1000) send_rx_frame(($urandom_range(1, 10) * 8) + $urandom_range(1, 7));
        // 3) rx + CRC corrupted (bits and bytes)
        $display("Testing Rx + CRC with corrupted data");
        repeat (1000) send_rx_frame($urandom_range(1, 10) * 8, 1'b1);

        // 4) tx without CRC (partial bytes + whole bytes)
        $display("Testing Tx without CRC");
        repeat (1000) send_tx_frame(($urandom_range(0, 10) * 8) + $urandom_range(0, 7), 1'b0);

        // 5) tx with CRC
        $display("Testing Tx + CRC");
        repeat (1000) send_tx_frame(($urandom_range(1, 10) * 8), 1'b1);

        // 6) FDT time
        // note that we test the FDT time in all the above cases too
        // but since we do all the Rx and then all the Tx, rx_last_bit is constant (per sim)
        // so we don another 1000 runs here, where rx_last_bit should toggle randomly
        $display("Testing FDT time");
        repeat (1000) begin
            // send a small rx frame so that rx_last_bit changes
            send_rx_frame($urandom_range(1,16));
            // send a small tx frame
            send_tx_frame($urandom_range(1,16), 1'b0);
        end

        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // check rx_crc_ok as expected on EOC
    rxCrcOkAsExpectedBits:
    assert property (
        @(posedge clk)
        ($rose(out_rx_iface_bits.eoc) && check_rx_crc_ok) |-> (rx_crc_ok == expect_rx_crc_ok))
        else $error("rx_crc_ok (%b) not as expected", rx_crc_ok);

    rxCrcOkAsExpectedBytes:
    assert property (
        @(posedge clk)
        ($rose(out_rx_iface_bytes.eoc) && check_rx_crc_ok) |-> (rx_crc_ok == expect_rx_crc_ok))
        else $error("rx_crc_ok (%b) not as expected", rx_crc_ok);


endmodule
