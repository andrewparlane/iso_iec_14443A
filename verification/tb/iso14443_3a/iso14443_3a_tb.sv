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

    rx_interface #(.BY_BYTE(0)) rx_iface_from_14443_2a  (.*);
    tx_interface #(.BY_BYTE(0)) tx_iface_to_14443_2a    (.*);

    rx_interface #(.BY_BYTE(1)) rx_iface_to_14443_4a    (.*);
    tx_interface #(.BY_BYTE(1)) tx_iface_from_14443_4a  (.*);

    logic                       rx_crc_ok;
    logic                       tx_append_crc_14443_4a;

    logic                       iso14443_4a_deselect;
    logic                       iso14443_4a_rats;
    logic                       iso14443_4a_tag_active;

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
    // The source for the rx_iface_from_14443_2a
    // --------------------------------------------------------------

    rx_interface_source rx_source_14443_2a
    (
        .clk    (clk),
        .iface  (rx_iface_from_14443_2a)
    );

    // --------------------------------------------------------------
    // The sink for the tx_iface_to_14443_2a
    // --------------------------------------------------------------

    tx_interface_sink tx_sink_14443_2a
    (
        .clk    (clk),
        .iface  (tx_iface_to_14443_2a)
    );

    // --------------------------------------------------------------
    // The source for the tx_iface_from_14443_4a
    // --------------------------------------------------------------

    tx_interface_source tx_source_14443_4a
    (
        .clk    (clk),
        .iface  (tx_iface_from_14443_4a)
    );

    // --------------------------------------------------------------
    // The sink for the rx_iface_to_14443_4a
    // --------------------------------------------------------------

    rx_interface_sink rx_sink_14443_4a
    (
        .clk    (clk),
        .iface  (rx_iface_to_14443_4a)
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
    always_ff @(posedge tx_iface_to_14443_2a.data_valid) begin: triggerBlock
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
    // So we must add them to the data we send (rx_iface_from_14443_2a) and
    // check and strip them from the data we receive (tx_iface_to_14443_2a).

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
            automatic logic         expect_14443_4a_rx_data;
            automatic string        initStateName = dut.initialisation_inst.state.name;

            expect_14443_4a_rx_data = ((dut.initialisation_inst.state == dut.initialisation_inst.State_PROTOCOL) ||
                                       (dut.initialisation_inst.state == dut.initialisation_inst.State_ACTIVE));

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
            rx_source_14443_2a.send_frame(bits, 0, error_in_bit);

            if (msg.add_crc && !msg.add_error) begin: addCRC
                crcOK: assert (rx_crc_ok) else $error("rx_crc_ok should be asserted");
            end

            // The frame encode won't start transmitting until the FDT triggers
            // which means we have to set the FDT timer running by pulsing pause_n_synchronised
            pause_n_synchronised <= 1'b0;
            @(posedge clk) begin end
            pause_n_synchronised <= 1'b1;

            // When in State_ACTIVE or State_PROTOCOL we should receive this data
            // in the rx_sink_14443_4a
            if (expect_14443_4a_rx_data) begin: expectPart4RxData
                automatic logic [7:0]   rx [$];
                automatic logic         rx_error;
                automatic int           rx_bits_in_last_byte;

                // check the sink
                rx_sink_14443_4a.wait_for_idle(16);
                rx                      = rx_sink_14443_4a.get_and_clear_received_queue();
                rx_error                = rx_sink_14443_4a.get_error_detected();
                rx_bits_in_last_byte    = rx_sink_14443_4a.get_bits_in_last_byte();

                rxError:
                assert (rx_error == msg.add_error)
                    else $error("rx_sink_14443_4a error state not as expected, got %b, expected %b",
                                rx_error, msg.add_error);

                if (!rx_error) begin
                    // set the not valid bits to 0 (same as in the rx_sink)
                    if (msg.bits_in_last_byte != 0) begin
                        for (int i = msg.bits_in_last_byte; i < 8; i++) begin
                            msg.data[$][i] = 1'b0;
                        end
                    end

                    rxAsExpected:
                    assert ((rx_bits_in_last_byte == msg.bits_in_last_byte) &&
                            (rx                   == msg.data))
                        else $error("rx_sink_14443_4a did not receive data as expected, got %p, bits_in_first_byte %d, expected %p",
                                    rx, rx_bits_in_last_byte, msg);
                end
            end
            else begin: dontExpectPart4RxData
                automatic logic [7:0] rx [$];

                // check the sink received nothing
                repeat (16) begin end
                rx = rx_sink_14443_4a.get_and_clear_received_queue();

                nothingReceived:
                assert (rx.size == 0) else $error("rx_sink_14443_4a received %p when init in state %s", rx, initStateName);
            end
        endtask

        task recv_frame (output MsgFromPICC msg, input logic expect_timeout=1'b0);
            automatic logic rx                  [$];
            automatic logic rx_without_parity   [$];
            automatic logic rx_verify           [$];

            // FDT timeout is max 236 ticks
            // the tx_sink_14443_2a requests new data every 5 ticks
            // max reply is AC reply with NVB = 0x20 -> 4 bytes UID + 1 byte BCC = 40 bits
            // 40*5 + 236 = 436 ticks
            // wait 1024
            if (!expect_timeout) begin
                tx_sink_14443_2a.wait_for_rx_complete(1024);
            end
            else begin
                // any rx must start before the FDT times out (max 236 ticks)
                repeat (256) @(posedge clk) begin end
            end

            msg.data                = '{};
            msg.bits_in_first_byte  = tx_sink_14443_2a.get_bits_in_first_byte() - 1; // - parity bit
            msg.has_crc             = 1'b0; // assume no CRC for now

            rx                      = tx_sink_14443_2a.get_and_clear_received_queue();

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
                State_IDLE:         isIdle:         assert ((dut.initialisation_inst.state == dut.initialisation_inst.State_IDLE)   && !dut.initialisation_inst.state_star) else $error("DUT not in correct state expected State_IDLE, 0 got %s, %b", dut.initialisation_inst.state.name, dut.initialisation_inst.state_star);
                State_READY:        isReady:        assert ((dut.initialisation_inst.state == dut.initialisation_inst.State_READY)  && !dut.initialisation_inst.state_star) else $error("DUT not in correct state expected State_READY, 0 got %s, %b", dut.initialisation_inst.state.name, dut.initialisation_inst.state_star);
                State_ACTIVE:       isActive:       assert ((dut.initialisation_inst.state == dut.initialisation_inst.State_ACTIVE) && !dut.initialisation_inst.state_star) else $error("DUT not in correct state expected State_ACTIVE, 0 got %s, %b", dut.initialisation_inst.state.name, dut.initialisation_inst.state_star);
                State_HALT:         isHalt:         assert ((dut.initialisation_inst.state == dut.initialisation_inst.State_IDLE)   && dut.initialisation_inst.state_star)  else $error("DUT not in correct state expected State_IDLE, 1 got %s, %b", dut.initialisation_inst.state.name, dut.initialisation_inst.state_star);
                State_READY_STAR:   isReadyStar:    assert ((dut.initialisation_inst.state == dut.initialisation_inst.State_READY)  && dut.initialisation_inst.state_star)  else $error("DUT not in correct state expected State_READY, 1 got %s, %b", dut.initialisation_inst.state.name, dut.initialisation_inst.state_star);
                State_ACTIVE_STAR:  isActiveStar:   assert ((dut.initialisation_inst.state == dut.initialisation_inst.State_ACTIVE) && dut.initialisation_inst.state_star)  else $error("DUT not in correct state expected State_ACTIVE, 1 got %s, %b", dut.initialisation_inst.state.name, dut.initialisation_inst.state_star);
                State_PROTOCOL:     isProtocol:     assert ((dut.initialisation_inst.state == dut.initialisation_inst.State_PROTOCOL))                                      else $error("DUT not in correct state expected State_PROTOCOL, 1 got %s, %b", dut.initialisation_inst.state.name, dut.initialisation_inst.state_star);
            endcase
        endfunction

        task send_and_verify_frame_from_part4;
            automatic logic [7:0]   data [$];
            automatic MsgFromPICC   reply;
            automatic logic         res;

            // The frame encode won't start transmitting until the FDT triggers
            // which means we have to set the FDT timer running by pulsing pause_n_synchronised
            pause_n_synchronised <= 1'b0;
            @(posedge clk) begin end
            pause_n_synchronised <= 1'b1;

            // send random data
            data                    = frame_generator_pkg::generate_byte_queue($urandom_range(1, 5));
            tx_append_crc_14443_4a  = 1'($urandom);
            tx_source_14443_4a.send_frame(data);

            // see if we receive it
            recv_frame(reply);

            // verify that the received data is correct
            res = (reply.data == data)                      &&
                  (reply.bits_in_first_byte == 0)           &&
                  (reply.has_crc == tx_append_crc_14443_4a);

            verifyPart4Tx:
            assert (res) else $error("Failed to correctly transmit from iso14443_4a");
        endtask
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
        tx_append_crc_14443_4a  = 1'b0;
        iso14443_4a_deselect    = 1'b0;
        iso14443_4a_rats        = 1'b0;

        rx_source_14443_2a.initialise;
        tx_sink_14443_2a.initialise;
        tx_sink_14443_2a.enable_expected_checking(1'b0);    // don't use the expected queue here
        tx_sink_14443_2a.enable_receive_queue(1'b1);        // use the receive queue instead

        tx_source_14443_4a.initialise;
        rx_sink_14443_4a.initialise;
        rx_sink_14443_4a.enable_expected_checking(1'b0);    // don't use the expected queue here
        rx_sink_14443_4a.enable_receive_queue(1'b1);        // use the receive queue instead

        tb_class = new();

        tb_class.do_reset;

        // Routing is tested as follows:
        //  Rx 14443_2a -> init     - tested by checking state transitions and replies
        //  Rx 14443_2a -> 14443_4a - tested in tb_class.send_frame by making sure the
        //                            rx_sink_14443_4a receives when and what it should
        //  Tx init     -> 14443_2a - tested by checking replies
        //  Tx 14443_4a -> 14443_2a - tested by faking the ATS reply

        // repeat 10 times with different UIDs
        repeat (10) begin
            // TODO: Add a parameter to let me instead test all possible variable_uid values
            //       For when running initialisation_tb_actual with UID_INPUT_BITS being small

            // randomise the variable part of the UID
            uid_variable = tb_class.randomise_uid;
            $display("UID_SIZE: %s, UID_INPUT_BITS: %d, UID_FIXED: 'b%b, Our UID: %h",
                     UID_SIZE.name, UID_INPUT_BITS, UID_FIXED, tb_class.get_uid);

            tb_class.run_all_initialisation_tests(100);

            // Test the transitions into and out of the PROTOCOL state
            $display("Transitions into and out of State_PROTOCOL");
            repeat (100) begin
                // check we can get into the PROTOCOL state by asserting iso14443_4a_rats
                // after sending a message from the ACTIVE / ACTIVE_STAR state.
                tb_class.go_to_state(1'($urandom) ? tb_class.State_ACTIVE
                                                  : tb_class.State_ACTIVE_STAR);

                // the actual RATS message is handled in the iso14443_4a module
                // all we care about here is that a message was recieved and the
                // iso14443_4a_rats signal is asserted
                tb_class.send_random;
                iso14443_4a_rats <= 1'b1;
                repeat (5) @(posedge clk) begin end
                iso14443_4a_rats <= 1'b0;
                tb_class.check_state(tb_class.State_PROTOCOL);

                // fake the ATS reply to check part4 Tx is routed correctly
                tb_class.send_and_verify_frame_from_part4;

                // check that there's no reply / state change to any message now
                repeat (10) begin
                    tb_class.send_msg(.REQA      (1'b1), .WUPA      (1'b1), .HLTA  (1'b1),
                                      .AC        (1'b1), .nAC       (1'b1),
                                      .SELECT    (1'b1), .nSELECT   (1'b1),
                                      .random    (1'b1), .error     (1'b1));
                    tb_class.check_no_reply;
                    tb_class.check_state(tb_class.State_PROTOCOL);
                end

                // check that we can exit this state by asserting iso14443_4a_deselect
                iso14443_4a_deselect <= 1'b1;
                @(posedge clk) begin end
                iso14443_4a_deselect <= 1'b0;

                tb_class.check_no_reply;
                tb_class.check_state(tb_class.State_HALT);
            end
        end

        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

    // once tx_iface_to_14443_2a.data_valid deasserts it can't reassert until after an Rx EOC
    rtsStaysLowUntilNextEOC:
    assert property (
        @(posedge clk)
        $fell(tx_iface_to_14443_2a.data_valid) |=>
            !tx_iface_to_14443_2a.data_valid throughout rx_iface_from_14443_2a.eoc[->1])
        else $error("tx_iface_to_14443_2a.data_valid asserted when not expected");

    // tx_iface_to_14443_2a.data_valid should be low during Rx
    rtsStaysLowDuringRx:
    assert property (
        @(posedge clk)
        $rose(rx_iface_from_14443_2a.soc) |=>
            !tx_iface_to_14443_2a.data_valid throughout rx_iface_from_14443_2a.eoc[->1])
        else $error("tx_iface_to_14443_2a.data_valid asserted during Rx");

    // check tag_active when the tag is in the active state
    tagActive:
    assert property (
        @(posedge clk)
        iso14443_4a_tag_active == (dut.initialisation_inst.state == dut.initialisation_inst.State_ACTIVE))
        else $error("iso14443_4a_tag_active not correct %b, dut in state %s",
                    iso14443_4a_tag_active, dut.initialisation_inst.state.name);

    // check tx_iface_from_14443_4a.req only asserts whilst in the ACTIVE or PROTOCOL state
    part4Req:
    assert property (
        @(posedge clk)
        tx_iface_from_14443_4a.req |->
            ((dut.initialisation_inst.state == dut.initialisation_inst.State_ACTIVE) ||
             (dut.initialisation_inst.state == dut.initialisation_inst.State_PROTOCOL)))
        else $error("tx_iface_from_14443_4a.req asserted while in state %s",
                    dut.initialisation_inst.state.name);


endmodule
