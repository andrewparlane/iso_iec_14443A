/***********************************************************************
        File: crc_control_tb
 Description: Testbench for crc_control
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

module crc_control_tb;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic           clk;
    logic           rst_n;

    logic           rx_crc_ok;

    logic           tx_append_crc;  // we only calculate the Tx CRC if we will use it
    logic           fdt_trigger;    // we only start the CRC calculation on the fdt_trigger
    logic [15:0]    crc;

    // interface
    rx_interface #(.BY_BYTE(0)) rx_iface (.*);
    tx_interface #(.BY_BYTE(0)) tx_iface (.*);

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    crc_control dut (.*);

    // --------------------------------------------------------------
    // The source for the rx_iface
    // --------------------------------------------------------------
    // we don't need a sink for the rx_iface because there are no signals
    // that go in the other direction
    rx_interface_source rx_source
    (
        .clk    (clk),
        .iface  (rx_iface)
    );

    // --------------------------------------------------------------
    // The source for the tx_iface
    // --------------------------------------------------------------

    tx_interface_source tx_source
    (
        .clk    (clk),
        .iface  (tx_iface)
    );

    // --------------------------------------------------------------
    // The sink for the tx_iface
    // --------------------------------------------------------------
    // since the tx_interface requires something to drive req we need a sink
    // the crc_control module just snoops the bus, it is not a sink
    tx_interface_sink tx_sink
    (
        .clk    (clk),
        .iface  (tx_iface)
    );

    // --------------------------------------------------------------
    // Clock generator
    // --------------------------------------------------------------

    // Calculate our clock period in ps
    localparam CLOCK_FREQ_HZ = 13560000; // 13.56MHz
    localparam CLOCK_PERIOD_PS = 1000000000000.0 / CLOCK_FREQ_HZ;
    initial begin
        clk = 1'b0;
        forever begin
            #(int'(CLOCK_PERIOD_PS/2))
            clk = ~clk;
        end
    end

    // --------------------------------------------------------------
    // Functions / Tasks
    // --------------------------------------------------------------

    // we need a task to send tx data, since we need to fire the fdt
    task send_tx_data (logic bits [$]);
        fork

            // process 1 - fires the fdt trigger
            begin
                // we need the trigger to fire on the same tick as data_valid asserts
                // so that the crc_control module has time to start the crc calculation
                // before the first req comes in.
                // An alternate option would be to make the tx_sink wait for a start signal
                // before starting to request data
                fdt_trigger <= 1'b1;
                @(posedge clk) begin end
                fdt_trigger <= 1'b0;
            end

            // process 2 - actually sends the data
            begin
                tx_source.send_frame(bits);
            end

        // block until both processes finish
        join
    endtask

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------
    logic           check_rx_crc_ok;
    logic           expect_rx_crc_ok;
    logic           check_tx_crc;
    logic [15:0]    expected_crc;
    logic           check_crc_stable;

    initial begin: testStimulus
        logic [7:0] data [$];
        logic       bits [$];

        rx_source.initialise;
        tx_source.initialise;
        tx_sink.initialise;

        tx_sink.enable_expected_checking(1'b0);

        check_tx_crc        = 1'b0;
        check_rx_crc_ok     = 1'b0;
        check_crc_stable    = 1'b0;

        tx_append_crc       = 1'b0;
        fdt_trigger         = 1'b0;

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // 1) rx_crc_ok after receiving:
        //  a) 8'h00, 8'h00, 8'hA0, 8'h1E   - given as an example in ISO/IEC 14443-3:2016 Annex B
        //  b) 8'h12, 8'h34, 8'h26, 8'hCF   - given as an example in ISO/IEC 14443-3:2016 Annex B
        //  c) 8'h63, 8'h63                 - inial CRC value for no data

        $display("Testing Rx with annex B examples");
        expect_rx_crc_ok    = 1'b1;
        check_rx_crc_ok     = 1'b1;
        check_tx_crc        = 1'b0;
        check_crc_stable    = 1'b0;

        data                = '{8'h00, 8'h00, 8'hA0, 8'h1E};
        bits                = frame_generator_pkg::convert_message_to_bit_queue_for_rx(data);
        rx_source.send_frame(bits);
        repeat (5) @(posedge clk) begin end

        data                = '{8'h12, 8'h34, 8'h26, 8'hCF};
        bits                = frame_generator_pkg::convert_message_to_bit_queue_for_rx(data);
        rx_source.send_frame(bits);
        repeat (5) @(posedge clk) begin end

        data                = '{8'h63, 8'h63};
        bits                = frame_generator_pkg::convert_message_to_bit_queue_for_rx(data);
        rx_source.send_frame(bits);
        repeat (5) @(posedge clk) begin end

        // 2) rx_crc_ok after sending random messages with CRC

        $display("Testing random Rx with valid CRC");
        expect_rx_crc_ok    = 1'b1;
        check_rx_crc_ok     = 1'b1;
        check_tx_crc        = 1'b0;
        check_crc_stable    = 1'b0;

        repeat (1000) begin
            automatic int num_bytes = $urandom_range(1, 20);
            data                = frame_generator_pkg::generate_byte_queue(num_bytes);
            data                = frame_generator_pkg::add_crc_to_message(data);
            bits                = frame_generator_pkg::convert_message_to_bit_queue_for_rx(data);
            rx_source.send_frame(bits);
            repeat (5) @(posedge clk) begin end
        end

        // 3) !rx_crc_ok after corrupting random bit in message

        $display("Testing random Rx with invalid CRC");
        expect_rx_crc_ok    = 1'b0;
        check_rx_crc_ok     = 1'b1;
        check_tx_crc        = 1'b0;
        check_crc_stable    = 1'b0;

        repeat (1000) begin
            automatic int num_bytes     = $urandom_range(1, 20);
            automatic int corrupt_bit   = $urandom_range(((num_bytes+2)*8) - 1);
            data                = frame_generator_pkg::generate_byte_queue(num_bytes);
            data                = frame_generator_pkg::add_crc_to_message(data);
            bits                = frame_generator_pkg::convert_message_to_bit_queue_for_rx(data);
            bits[corrupt_bit]   = !bits[corrupt_bit];
            rx_source.send_frame(bits);
            repeat (5) @(posedge clk) begin end
        end

        // 4) crc correct after sending:
        //  a) 8'h00, 8'h00                 - given as an example in ISO/IEC 14443-3:2016 Annex B
        //  b) 8'h12, 8'h34                 - given as an example in ISO/IEC 14443-3:2016 Annex B

        $display("Testing Tx with annex B examples");
        check_rx_crc_ok     = 1'b0;
        check_tx_crc        = 1'b1;
        tx_append_crc       = 1'b1;
        check_crc_stable    = 1'b0;

        data                = '{8'h00, 8'h00};
        bits                = frame_generator_pkg::convert_message_to_bit_queue_for_tx(data);
        expected_crc        = 16'h1EA0;
        send_tx_data(bits);
        repeat (5) @(posedge clk) begin end

        data                = '{8'h12, 8'h34};
        bits                = frame_generator_pkg::convert_message_to_bit_queue_for_tx(data);
        expected_crc        = 16'hCF26;
        send_tx_data(bits);
        repeat (5) @(posedge clk) begin end

        // 5) crc correct after sending random messages

        $display("Testing random Tx");
        check_rx_crc_ok     = 1'b0;
        check_tx_crc        = 1'b1;
        tx_append_crc       = 1'b1;
        check_crc_stable    = 1'b0;

        repeat (1000) begin
            automatic int num_bytes = $urandom_range(1, 20);
            data                = frame_generator_pkg::generate_byte_queue(num_bytes);
            bits                = frame_generator_pkg::convert_message_to_bit_queue_for_tx(data);
            expected_crc        = frame_generator_pkg::calculate_crc(data);
            send_tx_data(bits);
            repeat (5) @(posedge clk) begin end
        end

        // 6) crc remains stable after sending, if:
        //  a) fdt_trigger doesn't fire
        //  b) tx_append_crc is not asserted at the time of fdt_trigger
        //  c) tx_iface.data_valid is not asserted at the time of fdt_trigger

        $display("Testing CRC remains stable during Tx if various conditions don't occur");

        // note: if we are in Tx mode then even if we don't trigger the start of a new CRC
        //       for any of the above reasons, we'll continue modifying the CRC when each
        //       tx data bit goes through. (except in case b). So enter rx mode here first

        // enter rx mode
        check_rx_crc_ok     = 1'b0;
        check_tx_crc        = 1'b0;
        data                = frame_generator_pkg::generate_byte_queue(1);
        bits                = frame_generator_pkg::convert_message_to_bit_queue_for_rx(data);
        rx_source.send_frame(bits);
        repeat (5) @(posedge clk) begin end

        check_rx_crc_ok     = 1'b0;
        check_tx_crc        = 1'b0;
        tx_append_crc       = 1'b0;
        check_crc_stable    = 1'b1;

        // check case a) fdt_trigger doesn't fire
        data                = frame_generator_pkg::generate_byte_queue(5);
        bits                = frame_generator_pkg::convert_message_to_bit_queue_for_tx(data);
        tx_append_crc       = 1'b1; // tx_append_crc is 1
        tx_source.send_frame(bits); // data_valid is 1
                                    // no fdt
        repeat (5) @(posedge clk) begin end

        //  check case b) tx_append_crc is not asserted at the time of fdt_trigger
        data                = frame_generator_pkg::generate_byte_queue(5);
        bits                = frame_generator_pkg::convert_message_to_bit_queue_for_tx(data);
        tx_append_crc       = 1'b0; // tx_append_crc is 0
        send_tx_data(bits);         // data_valid is 1, fdt_trigger fires
        repeat (5) @(posedge clk) begin end

        //  check case c) tx_iface.data_valid is not asserted at the time of fdt_trigger
        data                = frame_generator_pkg::generate_byte_queue(5);
        bits                = frame_generator_pkg::convert_message_to_bit_queue_for_tx(data);
        tx_append_crc       = 1'b1;     // tx_append_crc is 1
        @(posedge clk) begin end
        fdt_trigger         <= 1'b1;    // fdt trigger fires, but data_valid is low
        @(posedge clk) begin end
        fdt_trigger         <= 1'b0;
        tx_source.send_frame(bits);     // data gets sent but fdt_trigger has already fired
        repeat (5) @(posedge clk) begin end

        // stop checking the crc is stable now
        check_crc_stable    = 1'b0;

        // 7) Rx followed by Tx to emulate Rx + reply

        $display("Testing random Rx followed by Tx");
        check_rx_crc_ok     = 1'b1;
        expect_rx_crc_ok    = 1'b1;
        check_tx_crc        = 1'b1;
        tx_append_crc       = 1'b1;
        check_crc_stable    = 1'b0;

        repeat (1000) begin
            begin // rx block
                automatic int num_bytes = $urandom_range(1, 20);
                data                = frame_generator_pkg::generate_byte_queue(num_bytes);
                data                = frame_generator_pkg::add_crc_to_message(data);
                bits                = frame_generator_pkg::convert_message_to_bit_queue_for_rx(data);
                rx_source.send_frame(bits);
                repeat (5) @(posedge clk) begin end
            end
            begin // tx block
                automatic int num_bytes = $urandom_range(1, 20);
                data                = frame_generator_pkg::generate_byte_queue(num_bytes);
                bits                = frame_generator_pkg::convert_message_to_bit_queue_for_tx(data);
                expected_crc        = frame_generator_pkg::calculate_crc(data);
                send_tx_data(bits);
                repeat (5) @(posedge clk) begin end
            end
        end

        // 8) Loopback Tx -> Rx

        $display("Testing looping back Tx to Rx");
        check_rx_crc_ok     = 1'b1;
        expect_rx_crc_ok    = 1'b1;
        check_tx_crc        = 1'b1;
        tx_append_crc       = 1'b1;
        check_crc_stable    = 1'b0;

        repeat (1000) begin
            automatic int num_bytes = $urandom_range(1, 20);

            // tx
            data                = frame_generator_pkg::generate_byte_queue(num_bytes);
            bits                = frame_generator_pkg::convert_message_to_bit_queue_for_tx(data);
            expected_crc        = frame_generator_pkg::calculate_crc(data);
            send_tx_data(bits);
            repeat (5) @(posedge clk) begin end

            // rx
            data.push_back(crc[7:0]);
            data.push_back(crc[15:8]);
            bits                = frame_generator_pkg::convert_message_to_bit_queue_for_rx(data);
            rx_source.send_frame(bits);
            repeat (5) @(posedge clk) begin end
        end

        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

    // check rx_crc_ok as expected on EOC
    rxCrcOkAsExpected:
    assert property (
        @(posedge clk)
        ($rose(rx_iface.eoc) && check_rx_crc_ok) |-> (rx_crc_ok == expect_rx_crc_ok))
        else $error("rx_crc_ok (%b) not as expected", rx_crc_ok);

    // check rx_crc_ok stable from EOC until either the next SOC or fdt_trigger
    logic next_frame_start;
    assign next_frame_start = rx_iface.soc || fdt_trigger;
    rxCrcOkStable:
    assert property (
        @(posedge clk)
        $rose(rx_iface.eoc) |-> $stable(rx_crc_ok) throughout next_frame_start[->1])
        else $error("rx_crc_ok is not stable between frames");

    // check crc as expected after tx finishes
    txCrcOk:
    assert property (
        @(posedge clk)
        ($fell(tx_iface.data_valid) && check_tx_crc) |=>
            (crc == expected_crc))
        else $error("crc (%x) not as expected (%x) after tx", crc, expected_crc);

    // check crc stable from falling edge of tx_iface.data_valid until either the next SOC or fdt_trigger
    txCrcStable:
    assert property (
        @(posedge clk)
        $fell(tx_iface.data_valid) |=>  ##1 ($stable(crc) throughout next_frame_start[->1]))
        else $error("crc is not stable between frames");

    // check crc stable when check_crc_stable is asserted
    txCrcStable2:
    assert property (
        @(posedge clk)
        $rose(check_crc_stable) |=> $stable(crc) throughout !check_crc_stable[->1])
        else $error("crc is not stable when check_crc_stable is asserted");

    // assert that rx_crc_ok is asserted iff (crc == 0)
    rxCrcOkIffCrc0:
    assert property (
        @(posedge clk)
        (rx_crc_ok == (crc == 0)))
        else $error("rx_crc_ok (%b) doesn't match (crc (%x) == 0)", rx_crc_ok, crc);

endmodule
