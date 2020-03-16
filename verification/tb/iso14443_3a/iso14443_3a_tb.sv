/***********************************************************************
        File: iso14443_3a_tb.sv
 Description: Testbench for the iso14443_3a module
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

module iso14443_3a_tb
#(
    // can't work out how to change enum parameters via command line arguments
    // use integers instead
    // 0 -> UIDSize_SINGLE, 1 -> UIDSize_DOUBLE, others -> UIDSize_TRIPLE
    parameter int UID_SIZE_CODE   = 0,

    // How many UID bits are variable (via the uid input port)?
    // defaults such that UID_FIXED has 2 bits
    parameter int UID_INPUT_BITS  = ISO14443A_pkg::get_uid_bits(init_comms_pkg::get_uid_size(UID_SIZE_CODE)) - 2,

    // don't overwrite this
    parameter int UID_FIXED_BITS  = ISO14443A_pkg::get_uid_bits(init_comms_pkg::get_uid_size(UID_SIZE_CODE)) - UID_INPUT_BITS,

    // The fixed bits of the UID (defaults to 0)
    parameter logic [UID_FIXED_BITS-1:0]    UID_FIXED       = '0
);

    import init_comms_pkg::init_comms_class;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    localparam TIMING_ADJUST = 1100;    // 1100 to speed up the simulation
    localparam ISO14443A_pkg::UIDSize UID_SIZE = init_comms_pkg::get_uid_size(UID_SIZE_CODE);

    logic                       clk;
    logic                       rst_n;

    // The variable part of the UID
    // should come from flash or dip switches / wire bonding / hardcoded
    // I assume this is constant in my code. So I'd recommend only changing it
    // while this IP core is in reset. That may not be strictly necesarry, but
    // further investigation would be necesarry to be sure.
    logic [UID_INPUT_BITS-1:0]  uid_variable;

    logic                       pause_n_synchronised;

    // Receive signals
    rx_interface #(.BY_BYTE(0)) in_rx_iface (.*);   // from 14443_2a
    rx_interface #(.BY_BYTE(1)) out_rx_iface (.*);  // to 14443_4
    logic                       rx_crc_ok;

    // Transmit signals
    tx_interface #(.BY_BYTE(0)) out_tx_iface (.*);  // to 14443_2a

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    iso14443_3a
    #(
        .UID_SIZE           (UID_SIZE),
        .UID_INPUT_BITS     (UID_INPUT_BITS),
        .UID_FIXED          (UID_FIXED),
        .FDT_TIMING_ADJUST  (TIMING_ADJUST)
    )
    dut (.*);

    // --------------------------------------------------------------
    // The source for the rx_iface
    // --------------------------------------------------------------

    rx_interface_source rx_source
    (
        .clk    (clk),
        .iface  (in_rx_iface)
    );

    // --------------------------------------------------------------
    // The sink for the tx_iface
    // --------------------------------------------------------------

    tx_interface_sink tx_sink
    (
        .clk    (clk),
        .iface  (out_tx_iface)
    );

    // --------------------------------------------------------------
    // Clock generator
    // --------------------------------------------------------------

    // Calculate our clock period in ps
    localparam CLOCK_FREQ_HZ = 10000000; // 10MHz (for ease of measureing the FDT)
    localparam CLOCK_PERIOD_PS = 1000000000000.0 / CLOCK_FREQ_HZ;
    initial begin
        clk = 1'b0;
        forever begin
            #(int'(CLOCK_PERIOD_PS/2))
            clk = ~clk;
        end
    end

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
    // Extend init_comms_pkg::init_comms_class and provide the
    // testbench specific functions / tasks
    // --------------------------------------------------------------

    // The difference here to the initialisation_tb is that the iso14443_3a
    // module checks and strips out parity bits on Rx, and adds them to Tx.
    // So we must add them to the data we send (in_rx_iface) and check and strip them
    // from the data we receive (out_tx_iface).

    class iso14443_3a_tb_class
    #(
        // What sized UID do we use?
        parameter ISO14443A_pkg::UIDSize        UID_SIZE,
        // How many UID bits are variable?
        parameter int                           UID_INPUT_BITS,
        // How many UID bits are fixed?
        parameter int                           UID_FIXED_BITS,
        // The fixed bits of the UID (defaults to 0)
        parameter logic [UID_FIXED_BITS-1:0]    UID_FIXED
    )
    extends init_comms_pkg::init_comms_class
    #(
        .UID_SIZE           (UID_SIZE),
        .UID_INPUT_BITS     (UID_INPUT_BITS),
        .UID_FIXED_BITS     (UID_FIXED_BITS),
        .UID_FIXED          (UID_FIXED)
    );

        task do_reset;
            rst_n <= 1'b0;
            @(posedge clk) begin end
            rst_n <= 1'b1;
            @(posedge clk) begin end
        endtask

        task send_frame (MsgFromPCD msg);
            automatic logic [15:0]  crc = frame_generator_pkg::calculate_crc(msg.data);
            automatic logic         bits[$];
            automatic int           error_in_bit = -1;

            if (msg.add_crc) begin
                msg.data.push_back(crc[7:0]);
                msg.data.push_back(crc[15:8]);
            end

            // get the bits to send
            bits = frame_generator_pkg::convert_message_to_bit_queue_for_rx(msg.data, msg.bits_in_last_byte);
            bits = frame_generator_pkg::add_parity_to_bit_queue(bits);

            // add an error?
            if (msg.add_error) begin
                error_in_bit = $urandom_range(0, bits.size); // not -1, the last error comes before the EOC
            end

            last_rx_bit = bits[$];
            rx_source.send_frame(bits, 0, error_in_bit);

            if (msg.add_crc && !msg.add_error) begin: addCRC
                crcOK: assert (rx_crc_ok) else $error("rx_crc_ok should be asserted");
            end
        endtask

        task recv_frame (output MsgFromPICC msg, input logic expect_timeout=1'b0);
            automatic logic rx                  [$];
            automatic logic rx_without_parity   [$];
            automatic logic rx_verify           [$];

            // The frame_encoder will never send until it gets the FDT trigger
            // which means we have to set the FDT timer running by pulsing pause_n_synchronised
            pause_n_synchronised <= 1'b0;
            @(posedge clk) begin end
            pause_n_synchronised <= 1'b1;

            // FDT timeout is max 236 ticks
            // the tx_sink requests new data every 5 ticks
            // max reply is AC reply with NVB = 0x20 -> 4 bytes UID + 1 byte BCC = 40 bits
            // 40*5 + 236 = 436 ticks
            // wait 1024
            if (!expect_timeout) begin
                tx_sink.wait_for_rx_complete(1024);
            end
            else begin
                // any rx must start before the FDT times out (max 236 ticks)
                repeat (256) @(posedge clk) begin end
            end

            msg.data                = '{};
            msg.bits_in_first_byte  = tx_sink.get_bits_in_first_byte() - 1; // - parity bit
            msg.has_crc             = 1'b0; // assume no CRC for now

            rx                      = tx_sink.get_and_clear_received_queue();

            // if we timed out, then we're done
            if (rx.size()) begin
                // data is what we received with the parity bits removed
                rx_without_parity       = frame_generator_pkg::remove_parity_from_bit_queue(rx, msg.bits_in_first_byte);

                // verify that the received parity bits were correct
                rx_verify               = frame_generator_pkg::add_parity_to_bit_queue(rx_without_parity, msg.bits_in_first_byte);
                //$display("rx: %p, without parity %p, with %p, bits_in_first_byte %d", rx, rx_without_parity, rx_verify, msg.bits_in_first_byte);
                parityOK: assert (rx == rx_verify) else $error("Parity fail, got %p, expected %p", rx, rx_verify);

                // convert the bit queue to a byte queue
                msg.data                = frame_generator_pkg::convert_bits_to_bytes(rx_without_parity, msg.bits_in_first_byte);
                //$display("data: %p", msg.data);
                // check if it has a CRC
                // CRC is two bytes, need at least one byte of data too
                if (msg.data.size >= 3) begin
                    automatic logic [15:0] crc = frame_generator_pkg::calculate_crc(msg.data[0:$-2]);
                    if ((crc[7:0]  == msg.data[$-1]) &&
                        (crc[15:8] == msg.data[$])) begin
                        // CRC is OK
                        msg.has_crc = 1'b1;
                        msg.data    = msg.data[0:$-2];  // remove the CRC
                    end
                    // we could have a CRC but it be wrong, but we will pick that up when we verify
                    // the reply.
                end
            end

            if (msg.bits_in_first_byte == 8) begin
                msg.bits_in_first_byte = 0;
            end
        endtask

        function void check_state (State state);
            case (state)
                State_IDLE:         isIdle:        assert ((dut.initialisation_inst.state == dut.initialisation_inst.State_IDLE)   && !dut.initialisation_inst.state_star) else $error("DUT not in correct state expected State_IDLE, 0 got %s, %b", dut.initialisation_inst.state.name, dut.initialisation_inst.state_star);
                State_READY:        isReady:       assert ((dut.initialisation_inst.state == dut.initialisation_inst.State_READY)  && !dut.initialisation_inst.state_star) else $error("DUT not in correct state expected State_READY, 0 got %s, %b", dut.initialisation_inst.state.name, dut.initialisation_inst.state_star);
                State_ACTIVE:       isActive:      assert ((dut.initialisation_inst.state == dut.initialisation_inst.State_ACTIVE) && !dut.initialisation_inst.state_star) else $error("DUT not in correct state expected State_ACTIVE, 0 got %s, %b", dut.initialisation_inst.state.name, dut.initialisation_inst.state_star);
                State_HALT:         isHalt:        assert ((dut.initialisation_inst.state == dut.initialisation_inst.State_IDLE)   && dut.initialisation_inst.state_star)  else $error("DUT not in correct state expected State_IDLE, 1 got %s, %b", dut.initialisation_inst.state.name, dut.initialisation_inst.state_star);
                State_READY_STAR:   isReadyStar:   assert ((dut.initialisation_inst.state == dut.initialisation_inst.State_READY)  && dut.initialisation_inst.state_star)  else $error("DUT not in correct state expected State_READY, 1 got %s, %b", dut.initialisation_inst.state.name, dut.initialisation_inst.state_star);
                State_ACTIVE_STAR:  isActiveStar:  assert ((dut.initialisation_inst.state == dut.initialisation_inst.State_ACTIVE) && dut.initialisation_inst.state_star)  else $error("DUT not in correct state expected State_ACTIVE, 1 got %s, %b", dut.initialisation_inst.state.name, dut.initialisation_inst.state_star);
            endcase
        endfunction
    endclass

    iso14443_3a_tb_class
    #(
        .UID_SIZE           (UID_SIZE),
        .UID_INPUT_BITS     (UID_INPUT_BITS),
        .UID_FIXED_BITS     (UID_FIXED_BITS),
        .UID_FIXED          (UID_FIXED)
    )
    tb_class;

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin
        // TODO: test message routing

        rx_source.initialise;
        tx_sink.initialise;
        tx_sink.enable_expected_checking(1'b0);    // don't use the expected queue here
        tx_sink.enable_receive_queue(1'b1);        // use the receive queue instead

        tb_class = new();

        tb_class.do_reset;

        // repeat 10 times with different UIDs
        repeat (10) begin
            // TODO: Add a parameter to let me instead test all possible variable_uid values
            //       For when running initialisation_tb_actual with UID_INPUT_BITS being small

            // randomise the variable part of the UID
            uid_variable = tb_class.randomise_uid;
            $display("UID_SIZE: %s, UID_INPUT_BITS: %d, UID_FIXED: 'b%b, Our UID: %h",
                     UID_SIZE.name, UID_INPUT_BITS, UID_FIXED, tb_class.get_uid);

            tb_class.run_all_initialisation_tests(100);
        end

        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

    // once tx_iface.data_valid deasserts it can't reassert until after an Rx EOC
    rtsStaysLowUntilNextEOC:
    assert property (
        @(posedge clk)
        $fell(out_tx_iface.data_valid) |=> !out_tx_iface.data_valid throughout in_rx_iface.eoc[->1])
        else $error("tx_iface.data_valid asserted when not expected");

    // tx_iface.data_valid should be low during Rx
    rtsStaysLowDuringRx:
    assert property (
        @(posedge clk)
        $rose(in_rx_iface.soc) |=> !out_tx_iface.data_valid throughout in_rx_iface.eoc[->1])
        else $error("tx_iface.data_valid asserted during Rx");

endmodule
