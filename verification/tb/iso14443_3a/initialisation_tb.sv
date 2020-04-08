/***********************************************************************
        File: initialisation_tb.sv
 Description: Testbench for the initialisation module
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

module initialisation_tb
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

    localparam ISO14443A_pkg::UIDSize UID_SIZE = init_comms_pkg::get_uid_size(UID_SIZE_CODE);

    logic                       clk;
    logic                       rst_n;

    // The variable part of the UID
    // should come from flash or dip switches / wire bonding / hardcoded
    // I assume this is constant in my code. So I'd recommend only changing it
    // while this IP core is in reset. That may not be strictly necesarry, but
    // further investigation would be necesarry to be sure.
    logic [UID_INPUT_BITS-1:0]  uid_variable;

    // Receive signals
    rx_interface #(.BY_BYTE(1)) rx_iface (.*);
    rx_interface #(.BY_BYTE(0)) rx_iface_bits (.*);
    logic                       rx_crc_ok;

    // Transmit signals
    tx_interface #(.BY_BYTE(1)) tx_iface (.*);
    logic                       tx_append_crc;

    // To/From the iso14443-4 block
    logic                       iso14443_4a_deselect;
    logic                       iso14443_4a_rats;
    logic                       iso14443_4a_tag_active;

    // Message routing controls
    logic                       route_rx_to_initialisation;
    logic                       route_rx_to_14443_4a;
    logic                       route_tx_from_14443_4a;

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    initialisation
    #(
        .UID_SIZE       (UID_SIZE),
        .UID_INPUT_BITS (UID_INPUT_BITS),
        .UID_FIXED      (UID_FIXED)
    )
    dut (.*);

    // --------------------------------------------------------------
    // The source for the rx_iface
    // --------------------------------------------------------------

    rx_interface_source rx_source
    (
        .clk    (clk),
        .iface  (rx_iface_bits)
    );

    // --------------------------------------------------------------
    // The sink for the tx_iface
    // --------------------------------------------------------------

    tx_interface_sink tx_sink
    (
        .clk    (clk),
        .iface  (tx_iface)
    );

    // --------------------------------------------------------------
    // The deserialiser as the source of the rx_iface_bytes
    // --------------------------------------------------------------

    deserialiser ds_inst
    (
        .clk        (clk),
        .rst_n      (rst_n),

        .in_iface   (rx_iface_bits),
        .out_iface  (rx_iface)
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
    // Extend init_comms_pkg::init_comms_class and provide the
    // testbench specific functions / tasks
    // --------------------------------------------------------------

    class initialisation_tb_class
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

            rx_crc_ok <= 1'b0;

            if (msg.add_crc) begin
                msg.data.push_back(crc[7:0]);
                msg.data.push_back(crc[15:8]);
            end

            // get the bits to send
            bits = frame_generator_pkg::convert_message_to_bit_queue_for_rx(msg.data, msg.bits_in_last_byte);

            // add an error?
            if (msg.add_error) begin
                error_in_bit = $urandom_range(0, bits.size); // not -1, the last error comes before the EOC
            end

            rx_source.send_frame(bits, 0, error_in_bit);

            // CRC
            if (msg.add_crc && !msg.add_error) begin
                rx_crc_ok <= 1'b1;
            end
        endtask

        task recv_frame (output MsgFromPICC msg, input logic expect_timeout=1'b0);
            // the tx_sink requestes new data every 5 ticks
            // assuming it takes 20 ticks to start sending (will be less)
            // max reply is AC reply with NVB = 0x20 -> 4 bytes UID + 1 byte BCC = 40 bits
            // 40*5 + 20 = 220 ticks
            // wait 500
            if (!expect_timeout) begin
                tx_sink.wait_for_rx_complete(500);
            end
            else begin
                // assume any rx will at least start within 50 ticks
                repeat (50) @(posedge clk) begin end
            end

            msg.data                = tx_sink.get_and_clear_received_queue();
            msg.bits_in_first_byte  = tx_sink.get_bits_in_first_byte();
            msg.has_crc             = tx_append_crc;
        endtask

        function void check_state (State state);
            case (state)
                State_IDLE:         isIdle:         assert ((dut.state == dut.State_IDLE)   && !dut.state_star) else $error("DUT not in correct state expected State_IDLE, 0 got %s, %b", dut.state.name, dut.state_star);
                State_READY:        isReady:        assert ((dut.state == dut.State_READY)  && !dut.state_star) else $error("DUT not in correct state expected State_READY, 0 got %s, %b", dut.state.name, dut.state_star);
                State_ACTIVE:       isActive:       assert ((dut.state == dut.State_ACTIVE) && !dut.state_star) else $error("DUT not in correct state expected State_ACTIVE, 0 got %s, %b", dut.state.name, dut.state_star);
                State_HALT:         isHalt:         assert ((dut.state == dut.State_IDLE)   && dut.state_star)  else $error("DUT not in correct state expected State_IDLE, 1 got %s, %b", dut.state.name, dut.state_star);
                State_READY_STAR:   isReadyStar:    assert ((dut.state == dut.State_READY)  && dut.state_star)  else $error("DUT not in correct state expected State_READY, 1 got %s, %b", dut.state.name, dut.state_star);
                State_ACTIVE_STAR:  isActiveStar:   assert ((dut.state == dut.State_ACTIVE) && dut.state_star)  else $error("DUT not in correct state expected State_ACTIVE, 1 got %s, %b", dut.state.name, dut.state_star);
                State_PROTOCOL:     isProtocol:     assert ((dut.state == dut.State_PROTOCOL))                  else $error("DUT not in correct state expected State_PROTOCOL, 1 got %s, %b", dut.state.name, dut.state_star);
            endcase
        endfunction
    endclass

    initialisation_tb_class
    #(
        .UID_SIZE           (UID_SIZE),
        .UID_INPUT_BITS     (UID_INPUT_BITS),
        .UID_FIXED_BITS     (UID_FIXED_BITS),
        .UID_FIXED          (UID_FIXED)
    )
    init_tb_class;

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin
        iso14443_4a_deselect    <= 1'b0;
        iso14443_4a_rats        <= 1'b0;

        rx_source.initialise;
        tx_sink.initialise;
        tx_sink.enable_expected_checking(1'b0);    // don't use the expected queue here
        tx_sink.enable_receive_queue(1'b1);        // use the receive queue instead

        init_tb_class   = new();

        init_tb_class.do_reset;

        // repeat 10 times with different UIDs
        repeat (10) begin
            // TODO: Add a parameter to let me instead test all possible variable_uid values
            //       For when running initialisation_tb_actual with UID_INPUT_BITS being small

            // randomise the variable part of the UID
            uid_variable = init_tb_class.randomise_uid;
            $display("UID_SIZE: %s, UID_INPUT_BITS: %d, UID_FIXED: 'b%b, Our UID: %h",
                     UID_SIZE.name, UID_INPUT_BITS, UID_FIXED, init_tb_class.get_uid);

            // Run the normal tests
            init_tb_class.run_all_initialisation_tests();

            // Test the transitions into and out of the PROTOCOL state
            $display("Transitions into and out of State_PROTOCOL");
            repeat (1000) begin
                // check we can get into the PROTOCOL state by asserting iso14443_4a_rats
                // after sending a message from the ACTIVE / ACTIVE_STAR state.
                init_tb_class.go_to_state(1'($urandom) ? init_tb_class.State_ACTIVE
                                                       : init_tb_class.State_ACTIVE_STAR);
                // the actual RATS message is handled in the iso14443_4a module
                // all we care about here is that a message was recieved and the
                // iso14443_4a_rats signal is asserted
                init_tb_class.send_random;
                iso14443_4a_rats <= 1'b1;
                repeat (5) @(posedge clk) begin end
                iso14443_4a_rats <= 1'b0;
                init_tb_class.check_state(init_tb_class.State_PROTOCOL);

                // check that there's no reply / state change to any message now
                repeat (10) begin
                    init_tb_class.send_msg(.REQA      (1'b1), .WUPA      (1'b1), .HLTA  (1'b1),
                                           .AC        (1'b1), .nAC       (1'b1),
                                           .SELECT    (1'b1), .nSELECT   (1'b1),
                                           .random    (1'b1), .error     (1'b1));
                    init_tb_class.check_no_reply;
                    init_tb_class.check_state(init_tb_class.State_PROTOCOL);
                end

                // check that we can exit this state by asserting iso14443_4a_deselect
                iso14443_4a_deselect <= 1'b1;
                @(posedge clk) begin end
                iso14443_4a_deselect <= 1'b0;

                init_tb_class.check_no_reply;
                init_tb_class.check_state(init_tb_class.State_HALT);
            end
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
        $fell(tx_iface.data_valid) |=> !tx_iface.data_valid throughout rx_iface.eoc[->1])
        else $error("tx_iface.data_valid asserted when not expected");

    // tx_iface.data_valid should be low during Rx
    rtsStaysLowDuringRx:
    assert property (
        @(posedge clk)
        $rose(rx_iface.soc) |=> !tx_iface.data_valid throughout rx_iface.eoc[->1])
        else $error("tx_iface.data_valid asserted during Rx");

    // check tag_active when the tag is in the active state
    tagActive:
    assert property (
        @(posedge clk)
        iso14443_4a_tag_active == (dut.state == dut.State_ACTIVE))
        else $error("iso14443_4a_tag_active not correct %b, dut in state %s", iso14443_4a_tag_active, dut.state.name);

    // check routing signals
    routingSignals:
    assert property (
        @(posedge clk)
        (route_rx_to_initialisation == (dut.state != dut.State_PROTOCOL))   &&
        (route_rx_to_14443_4a       == ((dut.state == dut.State_ACTIVE) ||
                                        (dut.state == dut.State_PROTOCOL))) &&
        (route_tx_from_14443_4a     == (dut.state == dut.State_PROTOCOL)))
        else $error("Routing signals are not correct, route_rx_to_initialisation %b, route_rx_to_14443_4 %b, route_tx_from_14443_4 %b when in state %s",
                    route_rx_to_initialisation, route_rx_to_14443_4a, route_tx_from_14443_4a, dut.state.name);

endmodule
