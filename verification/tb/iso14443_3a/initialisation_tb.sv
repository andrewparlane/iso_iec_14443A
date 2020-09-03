/***********************************************************************
        File: initialisation_tb.sv
 Description: Testbench for the initialisation module
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

module initialisation_tb
#(
    // can't work out how to change enum parameters via command line arguments
    // use integers instead
    // 0 -> UIDSize_SINGLE, 1 -> UIDSize_DOUBLE, others -> UIDSize_TRIPLE
    parameter int UID_SIZE_CODE   = 0,

    // How many UID bits are variable (via the uid input port)?
    // defaults such that UID_FIXED has 2 bits
    parameter int UID_INPUT_BITS  = ISO14443A_pkg::get_uid_bits(get_uid_size(UID_SIZE_CODE)) - 2,

    // don't overwrite this
    parameter int UID_FIXED_BITS  = ISO14443A_pkg::get_uid_bits(get_uid_size(UID_SIZE_CODE)) - UID_INPUT_BITS,

    // The fixed bits of the UID (defaults to 0)
    parameter logic [UID_FIXED_BITS-1:0]    UID_FIXED       = '0
);

    function ISO14443A_pkg::UIDSize get_uid_size (int code);
        return (code == 0) ? ISO14443A_pkg::UIDSize_SINGLE :
               (code == 1) ? ISO14443A_pkg::UIDSize_DOUBLE :
                             ISO14443A_pkg::UIDSize_TRIPLE;
    endfunction

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    localparam ISO14443A_pkg::UIDSize UID_SIZE = get_uid_size(UID_SIZE_CODE);

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
    // UID
    // --------------------------------------------------------------

    // our UID class instance
    uid_pkg::FixedSizeUID
    #(
        .UID_SIZE       (UID_SIZE),
        .UID_FIXED_BITS (UID_FIXED_BITS),
        .UID_FIXED      (UID_FIXED)
    ) picc_uid;

    // updated manually when we change picc_uid, it'd be nice to automate this
    logic [ISO14443A_pkg::get_uid_bits(UID_SIZE)-1:0] full_uid;

    // assign the variable part of the UID from the full UID (this goes to the DUT)
    assign uid_variable = full_uid[UID_INPUT_BITS-1:0];

    // --------------------------------------------------------------
    // The driver / queue for the rx_iface_bits
    // --------------------------------------------------------------

    // driver
    typedef rx_bit_iface_driver_pkg::RxBitIfaceDriver                   RxDriverType;
    RxDriverType                                                        driver;

    // Rx Transactions
    typedef rx_bit_transaction_pkg::RxBitTransaction                        RxTransType;
    typedef rx_transaction_converter_pkg::RxByteToBitTransactionConverter   RxTransConvType;

    // the send queue
    typedef RxTransType                                                 RxTransQueueType [$];
    typedef wrapper_pkg::Wrapper #(.Type(RxTransQueueType))             RxQueueWrapperType;
    RxQueueWrapperType                                                  send_queue;

    // --------------------------------------------------------------
    // The monitor for the tx_iface
    // --------------------------------------------------------------

    // monitor
    typedef tx_byte_iface_monitor_pkg::TxByteIfaceMonitor                   TxMonitorType;
    TxMonitorType                                                           monitor;

    // Tx Transactions
    typedef tx_byte_transaction_pkg::TxByteTransaction                      TxTransType;
    typedef tx_transaction_converter_pkg::TxByteToByteTransactionConverter  TxTransConvType;

    // and the recv_queue
    typedef TxTransType                                                     TxTransQueueType [$];
    typedef wrapper_pkg::Wrapper #(.Type(TxTransQueueType))                 TxQueueWrapperType;
    TxQueueWrapperType                                                      recv_queue;

    // sink driver
    tx_iface_sink_driver_pkg::TxByteIfaceSinkDriver                         sink_driver;

    // --------------------------------------------------------------
    // Clock generator
    // --------------------------------------------------------------

    clock_source clock_source_inst (.*);

    // --------------------------------------------------------------
    // The deserialiser as the source of the rx_iface_bytes
    // --------------------------------------------------------------
    // we want the bits and bytes going into initialisation comms
    // to match up. I could tweak the timings of an rx_byte_driver,
    // but this seems easier, and matches how the DUT will be used

    deserialiser ds_inst
    (
        .clk        (clk),
        .rst_n      (rst_n),

        .in_iface   (rx_iface_bits),
        .out_iface  (rx_iface)
    );

    // ----------------------------------------------------------------
    // Extend CommsTestsSequence to do TB specific stuff
    // ----------------------------------------------------------------

    class InitCommsTbSequence
    extends comms_tests_sequence_pkg::CommsTestsSequence
    #(
        .RxTransType        (RxTransType),
        .TxTransType        (TxTransType),
        .RxTransConvType    (RxTransConvType),
        .TxTransConvType    (TxTransConvType),
        .RxDriverType       (RxDriverType),
        .TxMonitorType      (TxMonitorType)
    );

        logic corrupt_crcs;

        // constructor
        function new(uid_pkg::UID               _picc_uid,
                     TransGenType               _rx_trans_gen,
                     TransGenType               _tx_trans_gen,
                     RxTransConvType            _rx_trans_conv,
                     TxTransConvType            _tx_trans_conv,
                     RxQueueWrapperType         _rx_send_queue,
                     TxQueueWrapperType         _tx_recv_queue,
                     RxDriverType               _rx_driver,
                     TxMonitorType              _tx_monitor,
                     int                        _reply_timeout);
            super.new(_picc_uid,
                      _rx_trans_gen,
                      _tx_trans_gen,
                      _rx_trans_conv,
                      _tx_trans_conv,
                      _rx_send_queue,
                      _tx_recv_queue,
                      _rx_driver,
                      _tx_monitor,
                      _reply_timeout,
                      100);             // TODO: Run optimised builds and test with more than 100 loops per test

            corrupt_crcs = 1'b0;
        endfunction

        virtual task do_reset;
            rst_n <= 1'b0;
            repeat (5) @(posedge clk) begin end
            rst_n <= 1'b1;
            repeat (5) @(posedge clk) begin end
        endtask

        function void sequence_callback(EventCode ec, int arg=0);
            //$display("callback: %s", ec.name);

            case (ec)
                EventCode_SENDING:  begin
                    // argument is an EventMessageID
                    automatic EventMessageID    mid             = EventMessageID'(arg);
                    // sending an Rx message, mark it as CRC OK
                    // this isn't perfect as it will only be asserted once all the data
                    // and the CRC have been received, but it's good enough for this test.
                    // The correct behaviour will be tested in iso14443_3a_tb
                    automatic logic set_crc = !corrupt_crcs;

                    //$display("message: %s", mid.name);

                    case (mid)
                        EventMessageID_REQA:                    rx_crc_ok = 1'b0;
                        EventMessageID_WUPA:                    rx_crc_ok = 1'b0;
                        EventMessageID_HLTA:                    rx_crc_ok = set_crc;
                        EventMessageID_AC:                      rx_crc_ok = 1'b0;
                        EventMessageID_SELECT:                  rx_crc_ok = set_crc;
                        EventMessageID_RANDOM_NON_VALID:        rx_crc_ok = set_crc;
                        EventMessageID_RATS:                    begin
                            rx_crc_ok           = set_crc;
                            // Fake the RATS signal from the part4 module
                            // only valid if the CRC is not corrupt
                            iso14443_4a_rats    = set_crc;
                        end
                        EventMessageID_PPS:                     rx_crc_ok = set_crc;
                        EventMessageID_STD_S_DESELECT:          rx_crc_ok = set_crc;
                        EventMessageID_STD_I_BLOCK_CHAINING:    rx_crc_ok = set_crc;
                        EventMessageID_STD_I_BLOCK_NO_CHAINING: rx_crc_ok = set_crc;
                        EventMessageID_STD_R_ACK:               rx_crc_ok = set_crc;
                        EventMessageID_STD_R_NAK:               rx_crc_ok = set_crc;
                        EventMessageID_STD_S_DESELECT:          rx_crc_ok = set_crc;
                        EventMessageID_STD_S_PARAMETERS:        rx_crc_ok = set_crc;
                        default:                                $error("Handle mid: %s", mid.name);
                    endcase
                end
                EventCode_SENT: begin
                    // clear the rx_crc_ok flag now that we are sent
                    rx_crc_ok           = 1'b0;

                    // clear RATS too if it were set
                    iso14443_4a_rats    = 1'b0;
                end
                EventCode_RECEIVED_OK: begin: ecRecevied
                    // received a reply from the PICC.
                    // argument is an EventMessageID
                    automatic EventMessageID    mid             = EventMessageID'(arg);
                    automatic logic             crc_expected    = 1'b1;

                    //$display("message: %s", mid.name);

                    case (mid)
                        EventMessageID_ATQA: begin
                            // ATQA does not have a CRC
                            crc_expected = 1'b0;
                        end
                        EventMessageID_AC_REPLY: begin
                            // AC reply does not have a CRC
                            crc_expected = 1'b0;
                        end
                        EventMessageID_SAK_NOT_COMPLETE:    begin end
                        EventMessageID_SAK_COMPLETE:        begin end
                        default: begin
                            $error("Handle mid: %s", mid.name);
                        end
                    endcase

                    // check the tx_append_crc signal is as expected
                    // this check isn't good enough as is, since tx_append_crc asserting
                    // after the frame has been sent out would not append a CRC.
                    // So we have another assert that checks that tx_append_crc only changes
                    // on the rising edge of tx_iface.data_valid
                    crcAsExpecetd: assert (tx_append_crc == crc_expected)
                        else $error("tx_append_crc %b expected %b after receiving %s",
                                    tx_append_crc, crc_expected, mid.name);
                end
                EventCode_RECEIVED_ERROR: begin
                    // nothing to do here
                end
                default: begin
                    $error("Handle event: %s", ec.name);
                end
            endcase
        endfunction

        function void specific_target_callback(SpecificTargetEventCode ec, int arg=0);
            if ((ec == SpecificTargetEventCode_ENTERED_STATE) ||
                (ec == SpecificTargetEventCode_REMAINING_IN_STATE)) begin
                automatic State state = State'(arg);
                //$display("Event Code %s, %s", ec.name, state.name);
                check_state(state);
            end
            else begin
                $error("Unknown event code %s", ec.name);
            end
        endfunction

        function void comms_tests_callback(CommsTestsEventCode ec, int arg=0);
            case (ec)
                CommsTestsEventCode_SET_CORRUPT_CRC: begin
                    // since we indicate CRCs are OK with rx_crc_ok we need to note not to do that
                    // when we are sending corrupt CRCs
                    corrupt_crcs = arg;
                end
                CommsTestsEventCode_SET_DRIVER_ERRORS: begin
                end
                default: begin
                    $error("Unknown event code %s", ec.name);
                end
            endcase
        endfunction

        function void check_state (State state);
            case (state)
                State_IDLE:                 isIdle:         assert ((dut.state == dut.State_IDLE)   && !dut.state_star) else $error("DUT not in correct state expected State_IDLE, 0 got %s, %b", dut.state.name, dut.state_star);
                State_READY:                isReady:        assert ((dut.state == dut.State_READY)  && !dut.state_star) else $error("DUT not in correct state expected State_READY, 0 got %s, %b", dut.state.name, dut.state_star);
                State_ACTIVE:               isActive:       assert ((dut.state == dut.State_ACTIVE) && !dut.state_star) else $error("DUT not in correct state expected State_ACTIVE, 0 got %s, %b", dut.state.name, dut.state_star);
                State_HALT:                 isHalt:         assert ((dut.state == dut.State_IDLE)   && dut.state_star)  else $error("DUT not in correct state expected State_IDLE, 1 got %s, %b", dut.state.name, dut.state_star);
                State_READY_STAR:           isReadyStar:    assert ((dut.state == dut.State_READY)  && dut.state_star)  else $error("DUT not in correct state expected State_READY, 1 got %s, %b", dut.state.name, dut.state_star);
                State_ACTIVE_STAR:          isActiveStar:   assert ((dut.state == dut.State_ACTIVE) && dut.state_star)  else $error("DUT not in correct state expected State_ACTIVE, 1 got %s, %b", dut.state.name, dut.state_star);
                State_PROTOCOL_PPS_ALLOWED: isProtocol1:    assert ((dut.state == dut.State_PROTOCOL))                  else $error("DUT not in correct state expected State_PROTOCOL, 1 got %s, %b", dut.state.name, dut.state_star);
                State_PROTOCOL_STD_COMMS:   isProtocol2:    assert ((dut.state == dut.State_PROTOCOL))                  else $error("DUT not in correct state expected State_PROTOCOL, 1 got %s, %b", dut.state.name, dut.state_star);
            endcase
        endfunction

        // override send_rats_verify_reply as nothing responds to the RATS message
        // we want to send it still as the DUT needs to receive a packet and see the iso14443_4a_rats
        // signal asserting to transiction into State_PROTOCOL
        task send_rats_verify_reply(logic [3:0] fsdi, logic [3:0] cid);
            send_rats(fsdi, cid);
            verify_no_reply;
        endtask

        // override send_std_s_deselect_verify_reply as nothing responds to the S(DESELECT) message
        // we still send it, and verify that the DUT doesn't reply
        // then we pulse the iso14443_4a_deselect signal. This is how it would work in
        // the full design.
        virtual task send_std_s_deselect_verify_reply(std_block_address_pkg::StdBlockAddress addr);
            send_std_s_deselect(addr);
            verify_no_reply;

            iso14443_4a_deselect <= 1'b1;
            @(posedge clk) begin end
            iso14443_4a_deselect <= 1'b0;
            @(posedge clk) begin end

            // since the state change happens after the reply has been sent out
            // we can't check for it during the send_std_s_deselect task as normal
            // so we do it in the wait_for_and_verify_std_s_deselect() task.
            // Except we don't call that here, so we need to manually register the state change
            register_state_change(State_HALT);
        endtask

        // not used in this test
        virtual function logic verify_dut_cid(logic [3:0] expected);
            return 1'b1;
        endfunction

        // not used in this test
        virtual function ByteQueue get_std_i_reply_inf(logic [7:0] inf [$]);
            return '{};
        endfunction

        // not used in this test
        virtual protected function void set_power_input(logic [1:0] _power);
        endfunction

    endclass

    InitCommsTbSequence seq;

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin
        automatic transaction_generator_pkg::TransactionGenerator   rx_trans_gen;
        automatic transaction_generator_pkg::TransactionGenerator   tx_trans_gen;
        automatic RxTransConvType                                   rx_trans_conv;
        automatic TxTransConvType                                   tx_trans_conv;

        iso14443_4a_deselect    <= 1'b0;
        iso14443_4a_rats        <= 1'b0;

        driver          = new(rx_iface_bits);
        monitor         = new(tx_iface);
        sink_driver     = new(tx_iface);

        send_queue      = new('{});
        recv_queue      = new('{});

        rx_trans_gen        = new(1'b1);    // Rx messages must have CRCs applied
        tx_trans_gen        = new(1'b0);    // Tx messages won't have CRCs added yet

        rx_trans_conv       = new(1'b0);    // Rx messages should not have parity bits here
        tx_trans_conv       = new;          // Tx messages are bytes so no parity bits

        picc_uid        = new('x);

        seq             = new(picc_uid,
                              rx_trans_gen,
                              tx_trans_gen,
                              rx_trans_conv,
                              tx_trans_conv,
                              send_queue,
                              recv_queue,
                              driver,
                              monitor,
                              100);         // longest reply is 5 bytes, sink_driver uses 16 ticks between reqs

        driver.start        (send_queue.data);
        monitor.start       (recv_queue.data);
        sink_driver.start   ();

        // repeat 10 times with different UIDs
        repeat (10) begin
            // TODO: Add a parameter to let me instead test all possible variable_uid values
            //       For when running initialisation_tb_actual with UID_INPUT_BITS being small

            // randomise the variable part of the UID
            picc_uid.randomize;
            full_uid = picc_uid.get_uid;
            $display("NOTE: New UID: %s", picc_uid.to_string);
            seq.do_reset;

            // Run the tests
            seq.run_all_initialisation_tests();
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

    // tx_append_crc should only change on the rising edge of tx_iface.data_valid
    txAppendCRCOnlyOnPosedgeDataValid:
    assert property (
        @(posedge clk)
        !$stable(tx_append_crc) |-> $rose(tx_iface.data_valid))
        else $error("tx_append_crc changed not on a rising edge of tx_iface.data_valid");

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
