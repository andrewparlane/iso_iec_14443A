/***********************************************************************
        File: iso14443_3a_tb.sv
 Description: Testbench for the iso14443_3a module
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

module iso14443_3a_tb
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

    localparam TIMING_ADJUST = 1100;    // 1100 to speed up the simulation
    localparam ISO14443A_pkg::UIDSize UID_SIZE = get_uid_size(UID_SIZE_CODE);

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
    // The driver / queue for the rx_iface_from_14443_2a
    // --------------------------------------------------------------

    // driver
    typedef rx_bit_iface_driver_pkg::RxBitIfaceDriver                   RxDriverType;
    RxDriverType                                                        rx_driver;

    // Rx Transactions
    typedef rx_bit_transaction_pkg::RxBitTransaction                        RxInTransType;
    typedef rx_transaction_converter_pkg::RxByteToBitTransactionConverter   RxTransConvType;

    // the send queue
    typedef RxInTransType                                               RxInTransQueueType [$];
    typedef wrapper_pkg::Wrapper #(.Type(RxInTransQueueType))           RxInQueueWrapperType;
    RxInQueueWrapperType                                                rx_send_queue;

    // --------------------------------------------------------------
    // The monitor for the rx_iface_to_14443_4a
    // --------------------------------------------------------------

    rx_byte_iface_monitor_pkg::RxByteIfaceMonitor                           rx_monitor;

    // the transaction generator for verifying received messages
    typedef rx_byte_transaction_pkg::RxMonitorByteTransaction               RxOutTransType;

    // and the recv_queue
    RxOutTransType                                                          rx_recv_queue [$];

    // --------------------------------------------------------------
    // The monitor for the tx_iface_to_14443_2a
    // --------------------------------------------------------------

    // monitor
    typedef tx_bit_iface_monitor_pkg::TxBitIfaceMonitor                 TxMonitorType;
    TxMonitorType                                                       tx_monitor;

    // Tx Transactions
    typedef tx_bit_transaction_pkg::TxBitTransaction                        TxOutTransType;
    typedef tx_transaction_converter_pkg::TxByteToBitTransactionConverter   TxTransConvType;

    // and the recv_queue
    typedef TxOutTransType                                              TxOutTransQueueType [$];
    typedef wrapper_pkg::Wrapper #(.Type(TxOutTransQueueType))          TxOutQueueWrapperType;
    TxOutQueueWrapperType                                               tx_recv_queue;

    // sink driver
    tx_iface_sink_driver_pkg::TxBitIfaceSinkDriver                      tx_sink_driver;

    // --------------------------------------------------------------
    // The driver / queue for the tx_iface_from_14443_4a
    // --------------------------------------------------------------

    // driver
    tx_byte_iface_source_driver_pkg::TxByteIfaceSourceDriver            tx_driver;

    // the send queue
    typedef tx_byte_transaction_pkg::TxByteTransaction                  TxInTransType;
    TxInTransType                                                       tx_send_queue[$];

    // --------------------------------------------------------------
    // Clock generator
    // --------------------------------------------------------------

    // Using 10MHz clock, so we can work with an integer period
    // avoiding timing errors generated due to the simulator only having ps accuracy
    // note: this won't be an issue in synthesis
    localparam real CLOCK_FREQ_HZ = 10000000.0; // 10MHz
    clock_source
    #(
        .CLOCK_FREQ_HZ (CLOCK_FREQ_HZ)
    )
    clock_source_inst (.*);

    localparam real CLOCK_PERIOD_PS = 1000000000000.0 / CLOCK_FREQ_HZ;

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
    assign last_rx_bit = dut.framing_inst.last_rx_bit;
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

    // trigger the pause_n_synchronised signal on the rx_iface_from_14443_2a.eoc signal
    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            pause_n_synchronised <= 1'b1;
        end
        else begin
            // only pulse for one tick
            pause_n_synchronised <= 1'b1;

            if (rx_iface_from_14443_2a.eoc) begin
                pause_n_synchronised <= 1'b0;
            end
        end
    end

    // ----------------------------------------------------------------
    // Extend CommsTestsSequence to do TB specific stuff
    // ----------------------------------------------------------------

    class ISO14443_3aTbSequence
    extends comms_tests_sequence_pkg::CommsTestsSequence
    #(
        .RxTransType        (RxInTransType),
        .TxTransType        (TxOutTransType),
        .RxTransConvType    (RxTransConvType),
        .TxTransConvType    (TxTransConvType),
        .RxDriverType       (RxDriverType),
        .TxMonitorType      (TxMonitorType)
    );

        // should we be checking rx_crc_ok?
        logic           corrupt_crcs;

        // when the initialisation module is in State_ACTIVE[_STAR] or State_PROTOCOL
        // messages are routed to both the initialisation module and the part4 module
        // we want to validate that the messages arrive correctly. We don't check every
        // message, because I don't have an easy way to know exactly what is sent
        // but in some cases such as RATS and S(DESELECT) I'm already overriding the
        // send_X_verify_relpy() tasks, so I can generate the expected message there.
        logic           check_rx_to_14443_4a;
        RxOutTransType  expected_rx_to_14443_4a;

        // Transaction generators for app level messages
        TransGenType    app_rx_trans_gen;

        // constructor
        function new(uid_pkg::UID               _picc_uid,
                     TransGenType               _rx_trans_gen,
                     TransGenType               _tx_trans_gen,
                     RxTransConvType            _rx_conv_gen,
                     TxTransConvType            _tx_conv_gen,
                     RxQueueWrapperType         _rx_send_queue,
                     TxQueueWrapperType         _tx_recv_queue,
                     RxDriverType               _rx_driver,
                     TxMonitorType              _tx_monitor,
                     int                        _reply_timeout);
            super.new(_picc_uid,
                      _rx_trans_gen,
                      _tx_trans_gen,
                      _rx_conv_gen,
                      _tx_conv_gen,
                      _rx_send_queue,
                      _tx_recv_queue,
                      _rx_driver,
                      _tx_monitor,
                      _reply_timeout,
                      100);             // TODO: Run optimised builds and test with more than 100 loops per test

            corrupt_crcs            = 1'b0;
            check_rx_to_14443_4a    = 1'b0;

            // the messages will contain the CRC at this point
            app_rx_trans_gen        = new(1'b1);
        endfunction

        virtual task do_reset;
            rst_n <= 1'b0;
            repeat (5) @(posedge clk) begin end
            rst_n <= 1'b1;
            repeat (5) @(posedge clk) begin end
        endtask

        function void sequence_callback(EventCode ec, int arg=0);
            case (ec)
                EventCode_SENDING:  begin
                    // argument is an EventMessageID
                    automatic EventMessageID mid = EventMessageID'(arg);

                    //$display("Sending %s", mid.name);

                    //$display("message: %s", mid.name);
                    if (mid == EventMessageID_RATS) begin
                        // Fake the RATS signal from the part4 module
                        // only valid if the CRC is not corrupt
                        iso14443_4a_rats = !corrupt_crcs;
                    end
                end
                EventCode_SENT: begin: ecSent
                    // argument is an EventMessageID
                    automatic EventMessageID    mid                 = EventMessageID'(arg);
                    automatic logic             check_crc           = 1'b0;
                    automatic logic             expect_forwarded;

                    //$display("Sent %s", mid.name);
                    // clear RATS if it were set
                    iso14443_4a_rats = 1'b0;

                    // verify that the rx_crc_ok signal is asserted if this was a message
                    // that should have a CRC
                    if (!corrupt_crcs && !rx_driver.get_add_error) begin
                        case(mid)
                            EventMessageID_REQA:                    begin end
                            EventMessageID_WUPA:                    begin end
                            EventMessageID_HLTA:                    check_crc = 1'b1;
                            EventMessageID_AC:                      begin end
                            EventMessageID_SELECT:                  check_crc = 1'b1;
                            EventMessageID_RATS:                    check_crc = 1'b1;
                            EventMessageID_PPS:                     check_crc = 1'b1;
                            EventMessageID_STD_S_DESELECT:          check_crc = 1'b1;
                            EventMessageID_STD_I_BLOCK_CHAINING:    check_crc = 1'b1;
                            EventMessageID_STD_I_BLOCK_NO_CHAINING: check_crc = 1'b1;
                            EventMessageID_STD_R_ACK:               check_crc = 1'b1;
                            EventMessageID_STD_R_NAK:               check_crc = 1'b1;
                            EventMessageID_STD_S_DESELECT:          check_crc = 1'b1;
                            EventMessageID_STD_S_PARAMETERS:        check_crc = 1'b1;
                            EventMessageID_RANDOM_NON_VALID:        check_crc = 1'b1;
                            default: begin
                                $error("Handle mid: %s", mid.name);
                            end
                        endcase
                    end

                    if (check_crc) begin: checkCRC
                        crcOK: assert (rx_crc_ok) else $error("rx_crc_ok = 0 when expecting 1");
                    end

                    // Depending on the state of the initialisation module, this message
                    // could be received the rx_monitor on the rx_iface_to_14443_4a interface.
                    // check that it has been received or not as expected.
                    // we don't actually check the message contents here, since we have no way
                    // of knowing what has been sent. The message contents are checked later in
                    // a specific test.
                    // NOTE: We assume it will have been already received by the monitor
                    //       due to the rx driver's ticks_after_transaction delay.
                    //       that should be set high enough to ensure any message is received
                    //       by the time we get here.

                    expect_forwarded = (picc_state == State_ACTIVE)                 ||
                                       (picc_state == State_ACTIVE_STAR)            ||
                                       (picc_state == State_PROTOCOL_PPS_ALLOWED)   ||
                                       (picc_state == State_PROTOCOL_STD_COMMS);

                    forwardedAsExpected:
                        assert (rx_recv_queue.size() == (expect_forwarded ? 1 : 0))
                        else $error("%d replies in the rx_recv_queue, expected %d",
                                     rx_recv_queue.size,
                                     (expect_forwarded ? 1 : 0));

                    // pop off any reply
                    if (rx_recv_queue.size() != 0) begin: forwadedTo14443_4a
                        automatic RxOutTransType    recv_trans  = rx_recv_queue.pop_front;
                        if (check_rx_to_14443_4a) begin: checkForwardedPkt
                            automatic logic res = recv_trans.compare(expected_rx_to_14443_4a);
                            iso144434aAsExpected:
                                assert (res)
                                else $error("Packet forwarded to rx_iface_to_14443_4a not as expected, received %s expected %s",
                                            recv_trans.to_string, expected_rx_to_14443_4a.to_string);
                        end
                    end
                end
                EventCode_RECEIVED_OK: begin
                    // nothing to do here
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
                State_IDLE:                 isIdle:         assert ((dut.initialisation_inst.state == dut.initialisation_inst.State_IDLE)   && !dut.initialisation_inst.state_star) else $error("DUT not in correct state expected State_IDLE, 0 got %s, %b",                   dut.initialisation_inst.state.name, dut.initialisation_inst.state_star);
                State_READY:                isReady:        assert ((dut.initialisation_inst.state == dut.initialisation_inst.State_READY)  && !dut.initialisation_inst.state_star) else $error("DUT not in correct state expected State_READY, 0 got %s, %b",                  dut.initialisation_inst.state.name, dut.initialisation_inst.state_star);
                State_ACTIVE:               isActive:       assert ((dut.initialisation_inst.state == dut.initialisation_inst.State_ACTIVE) && !dut.initialisation_inst.state_star) else $error("DUT not in correct state expected State_ACTIVE, 0 got %s, %b",                 dut.initialisation_inst.state.name, dut.initialisation_inst.state_star);
                State_HALT:                 isHalt:         assert ((dut.initialisation_inst.state == dut.initialisation_inst.State_IDLE)   && dut.initialisation_inst.state_star)  else $error("DUT not in correct state expected State_IDLE, 1 got %s, %b",                   dut.initialisation_inst.state.name, dut.initialisation_inst.state_star);
                State_READY_STAR:           isReadyStar:    assert ((dut.initialisation_inst.state == dut.initialisation_inst.State_READY)  && dut.initialisation_inst.state_star)  else $error("DUT not in correct state expected State_READY, 1 got %s, %b",                  dut.initialisation_inst.state.name, dut.initialisation_inst.state_star);
                State_ACTIVE_STAR:          isActiveStar:   assert ((dut.initialisation_inst.state == dut.initialisation_inst.State_ACTIVE) && dut.initialisation_inst.state_star)  else $error("DUT not in correct state expected State_ACTIVE, 1 got %s, %b",                 dut.initialisation_inst.state.name, dut.initialisation_inst.state_star);
                State_PROTOCOL_PPS_ALLOWED: isProtocol1:    assert ((dut.initialisation_inst.state == dut.initialisation_inst.State_PROTOCOL))                                      else $error("DUT not in correct state expected State_PROTOCOL_PPS_ALLOWED, got %s, %b",     dut.initialisation_inst.state.name, dut.initialisation_inst.state_star);
                State_PROTOCOL_STD_COMMS:   isProtocol2:    assert ((dut.initialisation_inst.state == dut.initialisation_inst.State_PROTOCOL))                                      else $error("DUT not in correct state expected State_PROTOCOL_STD_COMMS, got %s, %b",       dut.initialisation_inst.state.name, dut.initialisation_inst.state_star);
            endcase
        endfunction

        // override send_rats_verify_reply as the DUT does not respond to the RATS message
        // we want to send it still as the DUT needs to receive a packet and see the iso14443_4a_rats
        // signal asserting to transiction into State_PROTOCOL.
        task send_rats_verify_reply(logic [3:0] fsdi, logic [3:0] cid);
            // sending RATS, validate it on arrival on the rx_iface_to_14443_4a
            // note: this check only occurs if a packet is expected on that interface
            //       and one has actually been received
            check_rx_to_14443_4a    = 1'b1;
            expected_rx_to_14443_4a = RxOutTransType::create_from_rx_byte_transaction(app_rx_trans_gen.generate_rats(fsdi, cid));

            send_rats(fsdi, cid);
            verify_no_reply;

            check_rx_to_14443_4a    = 1'b0;
        endtask

        // override send_pps_verify_reply as the DUT does not respond to the PPS message
        // we still send it so we can verify it is routed correctly to the part4 block
        virtual task send_pps_verify_reply(logic p1_present, logic [1:0] dsi, logic [1:0] dri);
            automatic logic [3:0] cid = picc_target.get_cid();
            // sending PPS, validate it on arrival on the rx_iface_to_14443_4a
            // note: this check only occurs if a packet is expected on that interface
            //       and one has actually been received
            check_rx_to_14443_4a    = 1'b1;
            expected_rx_to_14443_4a = RxOutTransType::create_from_rx_byte_transaction(app_rx_trans_gen.generate_pps(cid, p1_present, dsi, dri));

            send_pps(cid, p1_present, dsi, dri);
            verify_no_reply;

            check_rx_to_14443_4a    = 1'b0;
        endtask

        // override send_std_s_deselect_verify_reply as the DUT does not respond to the
        // S(DESELECT) message we still send it, and verify that the DUT doesn't reply
        // then we pulse the iso14443_4a_deselect signal. This is how it would work in
        // the full design.
        virtual task send_std_s_deselect_verify_reply(std_block_address_pkg::StdBlockAddress addr);
            // sending RATS, validate it on arrival on the rx_iface_to_14443_4a
            // note: this check only occurs if a packet is expected on that interface
            //       and one has actually been received
            check_rx_to_14443_4a    = 1'b1;
            expected_rx_to_14443_4a = RxOutTransType::create_from_rx_byte_transaction(app_rx_trans_gen.generate_std_s_deselect_for_rx(addr));

            send_std_s_deselect(addr);
            verify_no_reply;

            iso14443_4a_deselect    <= 1'b1;
            @(posedge clk) begin end
            iso14443_4a_deselect    <= 1'b0;
            @(posedge clk) begin end

            // since the state change happens after the reply has been sent out
            // we can't check for it during the send_std_s_deselect task as normal
            // so we do it in the wait_for_and_verify_std_s_deselect() task.
            // Except we don't call that here, so we need to manually register the state change
            register_state_change(State_HALT);

            check_rx_to_14443_4a    = 1'b0;
        endtask

        // override this to add an extra test
        virtual task run_all_initialisation_tests;
            super.run_all_initialisation_tests;
            run_part4_tx_routing_tests;
        endtask

        task run_part4_tx_routing_tests;
            // Test that when in State_PROTOCOL_* messages transmitted on the
            // tx_iface_from_14443_4a is routed to the tx_iface_to_14443_2a
            // with CRC and parity bits added

            $display("State_PROTOCOL_* + routing from the iso14443-4a block");
            repeat (num_loops_per_test) begin
                // keep the length low, as the framing module will add 2 bytes of CRC
                // and we want out reply_timeout to be as low as possible since
                // that is directly related to simulation speed.
                automatic TxInTransType tx_send_trans   = TxInTransType::new_random_transaction($urandom_range(1,3), 0);
                automatic TxInTransType tx_expected     = new(tx_send_trans.data, tx_send_trans.bits_in_first_byte);

                go_to_state(1'($urandom) ? State_PROTOCOL_PPS_ALLOWED : State_PROTOCOL_STD_COMMS);

                // set whether we add a CRC or not to the Tx message
                tx_append_crc_14443_4a = 1'($urandom);

                // The FDT won't fire unless we send an Rx packet first
                send_random_non_valid;

                // fake a transmit from the part4 block
                tx_send_queue.push_back(tx_send_trans);

                // add the CRC if needed
                if (tx_append_crc_14443_4a) begin
                    tx_expected.append_crc;
                end

                wait_for_and_verify_trans(tx_expected, int'(EventMessageID_RANDOM_NON_VALID), "APP Tx");

                // confirm our state hasn't changed
                register_no_state_change;

                // re-enable auto adding CRCs in the tx_trans_gen
                tx_trans_gen.set_auto_append_crc(1'b1);
            end
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

    ISO14443_3aTbSequence seq;

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin
        automatic transaction_generator_pkg::TransactionGenerator   rx_trans_gen;
        automatic transaction_generator_pkg::TransactionGenerator   tx_trans_gen;
        automatic RxTransConvType                                   rx_trans_conv;
        automatic TxTransConvType                                   tx_trans_conv;
        automatic int                                               reply_timeout;

        tx_append_crc_14443_4a  = 1'b0;
        iso14443_4a_deselect    = 1'b0;
        iso14443_4a_rats        = 1'b0;

        rx_driver           = new(rx_iface_from_14443_2a);
        rx_monitor          = new(rx_iface_to_14443_4a);
        tx_monitor          = new(tx_iface_to_14443_2a);
        tx_driver           = new(tx_iface_from_14443_4a, 0, 256, 512);  // each byte is 8 bits + parity, sink driver sends req every 16 ticks
        tx_sink_driver      = new(tx_iface_to_14443_2a);

        rx_send_queue       = new('{});
        tx_recv_queue       = new('{});
        // tx_send_queue and rx_recv_queue are just queues and don't use the wrapper class
        rx_recv_queue       = '{};
        tx_send_queue       = '{};

        rx_trans_gen        = new(1'b1);    // Rx messages must have CRCs applied
        tx_trans_gen        = new(1'b1);    // Tx messages will have CRCs applied

        rx_trans_conv       = new(1'b1);    // Rx messages must have parity bits
        tx_trans_conv       = new(1'b1);    // Tx messages will have parity bits

        picc_uid            = new('x);

        // longest reply is 5 bytes, sink_driver uses 16 ticks between reqs
        // each byte has 8 bits + parity -> 45 bits -> 720 ticks.
        // then the FDT takes ~130 ticks to fire (in the worst case)
        reply_timeout   = 1024;
        seq             = new(picc_uid,
                              rx_trans_gen,
                              tx_trans_gen,
                              rx_trans_conv,
                              tx_trans_conv,
                              rx_send_queue,
                              tx_recv_queue,
                              rx_driver,
                              tx_monitor,
                              reply_timeout);

        rx_driver.start         (rx_send_queue.data);
        rx_monitor.start        (rx_recv_queue);
        tx_monitor.start        (tx_recv_queue.data);
        tx_driver.start         (tx_send_queue);
        tx_sink_driver.start    ();

        // Routing is tested as follows:
        //  Rx 14443_2a -> init     - tested by checking state transitions and replies
        //  Rx 14443_2a -> 14443_4a - tested by verifying RATS, PPS and S(DESELECT) are received OK
        //  Tx init     -> 14443_2a - tested by checking replies
        //  Tx 14443_4a -> 14443_2a - tested in run_part4_tx_routing_tests()

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
