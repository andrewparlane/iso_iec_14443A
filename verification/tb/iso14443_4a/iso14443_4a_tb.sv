/***********************************************************************
        File: iso14443_4a_tb.sv
 Description: Testbench for iso14443_4a
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

module iso14443_4a_tb;

    import std_block_address_pkg::StdBlockAddress;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic           clk;
    logic           rst_n;

    logic [1:0]     power;              // input

    logic           rx_crc_ok;          // input
    logic           tx_append_crc;      // output
    logic           tag_active;         // input
    logic           rx_rats;            // output
    logic           rx_deselect;        // output
    logic           app_resend_last;    // output

    rx_interface #(.BY_BYTE(1)) rx_iface (.*);
    tx_interface #(.BY_BYTE(1)) tx_iface (.*);
    rx_interface #(.BY_BYTE(1)) app_rx_iface (.*);
    tx_interface #(.BY_BYTE(1)) app_tx_iface (.*);

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    iso14443_4a dut (.*);

    // --------------------------------------------------------------
    // The driver / queue for the rx_iface
    // --------------------------------------------------------------

    // driver
    typedef rx_byte_iface_driver_pkg::RxByteIfaceDriver                     RxDriverType;
    RxDriverType                                                            rx_driver;

    // The transaction generator
    typedef rx_byte_transaction_pkg::RxByteTransaction                      RxInTransType;
    typedef rx_byte_transaction_generator_pkg::RxByteTransactionGenerator   RxTransGenType;
    RxTransGenType                                                          rx_trans_gen;

    // the send queue
    typedef RxInTransType                                                   RxInTransQueueType [$];
    typedef wrapper_pkg::Wrapper #(.Type(RxInTransQueueType))               RxInQueueWrapperType;
    RxInQueueWrapperType                                                    rx_send_queue;

    // --------------------------------------------------------------
    // The monitor for the app_rx_iface
    // --------------------------------------------------------------

    rx_byte_iface_monitor_pkg::RxByteIfaceMonitor                           app_rx_monitor;

    // and the recv_queue
    typedef rx_byte_transaction_pkg::RxMonitorByteTransaction               AppRxTransType;
    AppRxTransType                                                          app_rx_recv_queue [$];

    // --------------------------------------------------------------
    // The driver for the app_tx_iface
    // --------------------------------------------------------------

    // driver
    tx_byte_iface_source_driver_pkg::TxByteIfaceSourceDriver                app_tx_driver;

    // the send queue
    typedef tx_byte_transaction_pkg::TxByteTransaction                      AppTxTransType;
    AppTxTransType                                                          app_tx_send_queue[$];

    // --------------------------------------------------------------
    // The monitor for the tx_iface
    // --------------------------------------------------------------

    // monitor
    typedef tx_byte_iface_monitor_pkg::TxByteIfaceMonitor                   TxMonitorType;
    TxMonitorType                                                           tx_monitor;

    // Transaction generator
    typedef tx_byte_transaction_pkg::TxByteTransaction                      TxOutTransType;
    typedef tx_byte_transaction_generator_pkg::TxByteTransactionGenerator   TxTransGenType;
    TxTransGenType                                                          tx_trans_gen;

    // and the recv_queue
    typedef TxOutTransType                                                  TxOutTransQueueType [$];
    typedef wrapper_pkg::Wrapper #(.Type(TxOutTransQueueType))              TxOutQueueWrapperType;
    TxOutQueueWrapperType                                                   tx_recv_queue;

    // sink driver
    tx_iface_sink_driver_pkg::TxByteIfaceSinkDriver                         tx_sink_driver;

    // --------------------------------------------------------------
    // Clock generator
    // --------------------------------------------------------------

    clock_source clock_source_inst (.*);

    // ----------------------------------------------------------------
    // Assert rx_crc_ok when needed
    // ----------------------------------------------------------------
    // In the full design, this hapens on the last data byte in a frame
    // however we have no way to know when it will be the last data byte
    // so we set it on all data byte. This ensures it's set in the frame
    logic set_rx_crc_ok;
    always_ff @(posedge rx_iface.data_valid, negedge rst_n) begin
        if (!rst_n) begin
            rx_crc_ok <= 1'b0;
        end
        else begin
            rx_crc_ok <= set_rx_crc_ok;
        end
    end

    // ----------------------------------------------------------------
    // Extend CommsTestsSequence to do TB specific stuff
    // ----------------------------------------------------------------

    logic expect_rx_rats;
    logic expect_rx_deselect;
    logic expect_app_resend_last;

    class ISO14443_4aTbSequence
    extends comms_tests_sequence_pkg::CommsTestsSequence
    #(
        .RxTransType    (RxInTransType),
        .TxTransType    (TxOutTransType),
        .RxDriverType   (RxDriverType),
        .TxMonitorType  (TxMonitorType)
    );

        // should we be setting rx_crc_ok?
        logic       corrupt_crcs;

        // we need to know if the last sent message was a valid STD I-Block for the DUT.
        // Then if an R(ACK/NAK) is sent with the wronge block number we can verify app_resend_last
        // and actually resend the last reply from the app.
        logic       last_sent_was_valid_std_i_block;

        // To be able to resend the last app response, we need to cache what it was
        logic [7:0] app_last_sent_inf [$];

        // constructor
        function new(RxTransGenType             _rx_trans_gen,
                     TxTransGenType             _tx_trans_gen,
                     RxQueueWrapperType         _rx_send_queue,
                     TxQueueWrapperType         _tx_recv_queue,
                     RxDriverType               _rx_driver,
                     TxMonitorType              _tx_monitor,
                     int                        _reply_timeout);

            // UID is not used in part4 comms
            const static uid_pkg::UID dummy_uid = uid_pkg::UID::new_single_uid(32'h0);

            super.new(dummy_uid,
                      _rx_trans_gen,
                      _tx_trans_gen,
                      _rx_send_queue,
                      _tx_recv_queue,
                      _rx_driver,
                      _tx_monitor,
                      _reply_timeout,
                      1000);             // TODO: Run optimised builds and test with more than 1000 loops per test

            corrupt_crcs                    = 1'b0;
            last_sent_was_valid_std_i_block = 1'b0;
            app_last_sent_inf               = '{};
        endfunction

        virtual protected task do_reset;
            rst_n <= 1'b0;
            repeat (5) @(posedge clk) begin end
            rst_n <= 1'b1;
            repeat (5) @(posedge clk) begin end
        endtask

        function void sequence_callback(EventCode ec, int arg=0);
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
                        EventMessageID_REQA:                    set_rx_crc_ok = 1'b0;
                        EventMessageID_WUPA:                    set_rx_crc_ok = 1'b0;
                        EventMessageID_HLTA:                    set_rx_crc_ok = set_crc;
                        EventMessageID_AC:                      set_rx_crc_ok = 1'b0;
                        EventMessageID_SELECT:                  set_rx_crc_ok = set_crc;
                        EventMessageID_RANDOM_NON_VALID:        set_rx_crc_ok = set_crc;
                        EventMessageID_RATS:                    set_rx_crc_ok = set_crc;
                        EventMessageID_PPS:                     set_rx_crc_ok = set_crc;
                        EventMessageID_STD_S_DESELECT:          set_rx_crc_ok = set_crc;
                        EventMessageID_STD_I_BLOCK_CHAINING:    set_rx_crc_ok = set_crc;
                        EventMessageID_STD_I_BLOCK_NO_CHAINING: set_rx_crc_ok = set_crc;
                        EventMessageID_STD_R_ACK:               set_rx_crc_ok = set_crc;
                        EventMessageID_STD_R_NAK:               set_rx_crc_ok = set_crc;
                        EventMessageID_STD_S_DESELECT:          set_rx_crc_ok = set_crc;
                        EventMessageID_STD_S_PARAMETERS:        set_rx_crc_ok = set_crc;
                        default:                                $error("Handle mid: %s", mid.name);
                    endcase
                end
                EventCode_SENT: begin: ecSent
                    // argument is an EventMessageID
                    automatic EventMessageID mid = EventMessageID'(arg);
                    //$display("Sent %s", mid.name);

                    // done, clear the flags
                    expect_rx_rats  = 1'b0;
                    tag_active      = 1'b0;

                    // clear this here, if we have actually just finished sending a valid STD I-Block
                    // then this was called indirectly from the overridden send_std_i_block() below.
                    // Once we return to that, we'll set this flag if it were in fact a valid
                    // STD I-Block for the PICC.
                    last_sent_was_valid_std_i_block = 1'b0;

                    // check that this message was not forwarded to the app
                    // except in the case of the STD I-Block message which if valid
                    // should be forwarded and is verified in the overriden
                    // send_std_i_block task below
                    if ((mid != EventMessageID_STD_I_BLOCK_CHAINING) &&
                        (mid != EventMessageID_STD_I_BLOCK_NO_CHAINING)) begin
                        check_not_forwarded_to_app;
                    end
                end
                EventCode_RECEIVED_OK: begin
                    // clear flags
                    expect_app_resend_last = 1'b0;
                end
                EventCode_RECEIVED_ERROR: begin
                    // clear flags
                    expect_app_resend_last = 1'b0;
                end
                default: begin
                    $error("Handle event: %s", ec.name);
                end
            endcase
        endfunction

        // we don't check state in this TB. There are only 3 states of interest
        // and we verify those by sending invalid messages and checking they are ignored
        /* function void specific_target_callback(SpecificTargetEventCode ec, int arg=0);
            if ((ec == SpecificTargetEventCode_ENTERED_STATE) ||
                (ec == SpecificTargetEventCode_REMAINING_IN_STATE)) begin
                automatic State state = State'(arg);
                //$display("Event Code %s, %s", ec.name, state.name);
                check_state(state);
            end
            else begin
                $error("Unknown event code %s", ec.name);
            end
        endfunction */

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

        virtual task send_rats(logic [3:0] fsdi, logic [3:0] cid);
            if (!corrupt_crcs && !rx_driver.get_add_error && (cid != 15)) begin
                expect_rx_rats = 1'b1;
            end

            super.send_rats(fsdi, cid);

            expect_rx_rats = 1'b0;
        endtask

        // override send_std_i_block, and verify that the inf field + CRC are forwarded to the ap
        virtual task send_std_i_block(StdBlockAddress addr, logic chaining, logic block_num, logic [7:0] inf [$]);
            super.send_std_i_block(addr, chaining, block_num, inf);

            if (picc_target.is_for_us(addr) && !chaining &&
                ((picc_state == State_PROTOCOL_PPS_ALLOWED) ||
                 (picc_state == State_PROTOCOL_STD_COMMS))) begin
                // check this was forwarded to the app, and send the reply
                // corrupted CRCs get turned into errors on app_rx_iface
                // errors on rx_iface either get forwarded to app_rx_iface or nothing is
                // forwarded to the app. Depending on where the error occurs.
                if (rx_driver.get_add_error) begin
                    check_not_forwarded_to_app_or_has_error;
                end
                else if (corrupt_crcs) begin
                    check_forwarded_to_app(inf, 1'b1);
                end
                else begin
                    last_sent_was_valid_std_i_block = 1'b1;
                    check_forwarded_to_app(inf);
                    app_last_sent_inf = get_std_i_reply_inf(inf);
                    send_std_i_block_reply(app_last_sent_inf);
                end
            end
            else begin
                // check it wasn't forwarded to the app
                check_not_forwarded_to_app;
            end
        endtask

        virtual task send_std_r_ack(StdBlockAddress addr, logic block_num);
            if ((picc_target.get_picc_block_num() == block_num) &&
                last_sent_was_valid_std_i_block) begin

                // If the PCD receives an R(ACK/NAK) with block num the same as
                // it's current block num, then it should resend it's last reply
                expect_app_resend_last = 1'b1;
            end

            super.send_std_r_ack(addr, block_num);

            if (expect_app_resend_last) begin
                // resend the last app message
                send_std_i_block_reply(app_last_sent_inf);
            end
        endtask

        virtual task send_std_r_nak(StdBlockAddress addr, logic block_num);
            if ((picc_target.get_picc_block_num() == block_num) &&
                last_sent_was_valid_std_i_block) begin

                // If the PCD receives an R(ACK/NAK) with block num the same as
                // it's current block num, then it should resend it's last reply
                expect_app_resend_last = 1'b1;
            end

            super.send_std_r_nak(addr, block_num);

            if (expect_app_resend_last) begin
                // resend the last app message
                send_std_i_block_reply(app_last_sent_inf);
            end
        endtask

        // override send_std_s_deselect_verify_reply to check for the std_deselect signal
        virtual task send_std_s_deselect_verify_reply(StdBlockAddress addr);
            expect_rx_deselect = 1'b1;
            super.send_std_s_deselect_verify_reply(addr);
            expect_rx_deselect = 1'b0;
        endtask

        // override state transition tasks, as many aren't relevant for just the part4 module
        virtual protected task go_to_state_idle;
            do_reset;
            register_state_change(State_IDLE);
        endtask

        virtual protected task go_to_state_ready;
            go_to_state_idle;
            register_state_change(State_READY);
        endtask

        virtual protected task go_to_state_active;
            go_to_state_ready;

            // fake the tag_active signal from the initialisation module
            tag_active = 1'b1;
            register_state_change(State_ACTIVE);
        endtask

        virtual protected task go_to_state_halt;
            do_reset;
            register_state_change(State_HALT);
        endtask

        virtual protected task go_to_state_ready_star;
            go_to_state_halt;
            register_state_change(State_READY_STAR);
        endtask

        virtual protected task go_to_state_active_star;
            go_to_state_ready_star;

            // fake the tag_active signal from the initialisation module
            tag_active = 1'b1;
            register_state_change(State_ACTIVE_STAR);
        endtask

        virtual function ByteQueue get_std_i_reply_inf(logic [7:0] inf [$]);
            // respond with +1
            foreach(inf[i]) begin
                inf[i] = inf[i] + 1'd1;
            end
            return inf;
        endfunction

        virtual protected function void set_power_input(logic [1:0] _power);
            power = _power;
        endfunction

        virtual function logic verify_dut_cid(logic [3:0] expected);
            cidAsExpected:
            assert(dut.our_cid == expected) else $error("DUT's CID is %d expected %d", dut.our_cid, expected);
            return dut.our_cid == expected;
        endfunction

        virtual task wait_for_app_rx(output ready, output AppRxTransType trans, input logic expect_timeout=1'b0);
            if (!app_rx_monitor.idle) begin
                app_rx_monitor.wait_for_packet_received(128, !expect_timeout);
            end

            // we don't assert here, the caller should assert if needed

            ready = 1'b0;
            if (app_rx_recv_queue.size()) begin
                ready = 1'b1;
                trans = app_rx_recv_queue.pop_front;
            end
        endtask

        virtual protected function void check_not_forwarded_to_app;
            notForwarded:
            assert (app_rx_monitor.idle && (app_rx_recv_queue.size() == 0))
                else $error("Message forwarded to the app when not expected");

            if (app_rx_recv_queue.size() != 0) begin
                $display("INFO: got %s when nothing expected", app_rx_recv_queue[0].to_string);
                void'(app_rx_recv_queue.pop_front);
            end
        endfunction

        virtual protected task check_not_forwarded_to_app_or_has_error;
            automatic logic             ready;
            automatic AppRxTransType    trans;
            wait_for_app_rx(ready, trans, 1'b1);    // allow timeout

            if (ready) begin
                // don't care about the data, just check there's an error
                void'(verify_forwarded_to_app(trans, '{}, 1'b1));
            end
        endtask

        virtual protected task check_forwarded_to_app(logic [7:0] inf [$], logic expect_error=1'b0);
            automatic logic             ready;
            automatic AppRxTransType    trans;
            wait_for_app_rx(ready, trans, 1'b0);

            forwardedToApp: assert (ready) else $error("Message not forwarded to the app");

            if (ready) begin
                void'(verify_forwarded_to_app(trans, inf, expect_error));
            end
        endtask

        virtual protected function logic verify_forwarded_to_app(AppRxTransType trans, logic [7:0] inf [$], logic expect_error=1'b0);
            automatic AppRxTransType    expected = new(inf, 0, expect_error);
            automatic logic             res;

            // the farwarded message is the inf field plus the CRC of the whole message
            // (including the header which is not forwarded). We don't care about the CRC here
            // so pop it off, unless we're expecting an error in which case don't bother, since
            // we only care about the error flag, and the received data may be less than two bytes
            if (!expect_error) begin
                void'(trans.pop_back());
                void'(trans.pop_back());
            end

            res = trans.compare(expected);

            appMsgAsExpected:
            assert (res)
            else $error("Message forwarded to app not as expected, received %s expected %s",
                        trans.to_string, expected.to_string);

            return res;
        endfunction

        virtual protected task send_std_i_block_reply(logic [7:0] reply_inf [$]);
            // fake a reply to a STD I-block
            automatic AppTxTransType trans = new(reply_inf);
            app_tx_send_queue.push_back(trans);
        endtask
    endclass

    ISO14443_4aTbSequence seq;

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin
        automatic int reply_timeout;

        rx_driver           = new(rx_iface);
        app_rx_monitor      = new(app_rx_iface);
        app_tx_driver       = new(app_tx_iface, 0, 32, 32);
        tx_monitor          = new(tx_iface);
        tx_sink_driver      = new(tx_iface);

        rx_send_queue       = new('{});
        tx_recv_queue       = new('{});
        // app_tx_send_queue and app_rx_recv_queue are just queues and don't use the wrapper class
        app_rx_recv_queue   = '{};
        app_tx_send_queue   = '{};

        rx_trans_gen     = new(1'b1);   // auto append CRCs
        tx_trans_gen     = new(1'b0);   // Tx messages don't have CRCs at this point

        // longest valid reply is a STD I-Block with a max of 10 byte INF.
        // and a 2 byte header (PCB + CID). the tx_sink_driver reqs every 16 ticks
        reply_timeout   = 256;
        seq             = new(rx_trans_gen,
                              tx_trans_gen,
                              rx_send_queue,
                              tx_recv_queue,
                              rx_driver,
                              tx_monitor,
                              reply_timeout);

        rx_driver.start         (rx_send_queue.data);
        app_rx_monitor.start    (app_rx_recv_queue);
        app_tx_driver.start     (app_tx_send_queue);
        tx_monitor.start        (tx_recv_queue.data);
        tx_sink_driver.start    ();

        power                       = 2'b00;
        tag_active                  = 1'b0;
        set_rx_crc_ok               = 1'b1;

        expect_rx_rats              = 1'b0;
        expect_rx_deselect          = 1'b0;
        expect_app_resend_last      = 1'b0;

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        seq.run_all_part4_tests;

        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

    // check signals in reset
    inReset:
    assert property (
        @(posedge clk)
        !rst_n |-> (!rx_rats && !rx_deselect && !app_resend_last))
        else $error("signals in reset not as expected");

    // tx_append_crc should always be set
    txAppendCRC:
    assert property (@(posedge clk) tx_append_crc)
        else $error("tx_append_crc should always be set");

    // check rx_rats is as expected one tick after EOC (when the initialisation
    // module needs to samples it)
    rxRatsWhenExpected:
    assert property (
        @(posedge clk)
        $rose(rx_iface.eoc) |=> (rx_rats == expect_rx_rats))
        else $error("On EOC rx_rats %b not as expected %b", rx_rats, expect_rx_rats);

    // check app_resend_last only asserts when expected
    appResendLastOnlyWhenExpected:
    assert property (
        @(posedge clk)
        $rose(app_resend_last) |-> expect_app_resend_last)
        else $error("app_resend_last asserted when not expected");

    // check rx_deselect only asserts when expected
    rxDeselectOnlyWhenExpected:
    assert property (
        @(posedge clk)
        $rose(rx_deselect) |-> expect_rx_deselect)
        else $error("rx_deselect asserted when not expected");

    // check rx_deselect asserts when expected
    rxDeselectWhenExpected:
    assert property (
        @(posedge clk)
        $rose(expect_rx_deselect) |=> expect_rx_deselect throughout rx_deselect[->1])
        else $error("rx_deselect didn't assert when expected");

    // check rx_deselect only asserts for one tick at a time
    rxDeselectOneTick:
    assert property (
        @(posedge clk)
        $rose(rx_deselect) |=> $fell(rx_deselect))
        else $error("rx_deselect asserted for more than one tick at a time");

    // check rx_deselect does not asserts in the middle of a frame (rx / tx)
    rxDeselectDuringTx:
    assert property (
        @(posedge clk)
        rx_deselect |-> !tx_iface.data_valid)
        else $error("rx_deselect asserted when tx_iface.data_valid was asserted");

    // check app_resend_last only asserts for one tick at a time
    appResendLastOneTick:
    assert property (
        @(posedge clk)
        $rose(app_resend_last) |=> $fell(app_resend_last))
        else $error("app_resend_last asserted for more than one tick at a time");

    // check tx_iface.data_bits is always 0
    dataBitsAlways0:
    assert property (
        @(posedge clk)
        (tx_iface.data_bits == 0))
        else $error("tx_iface.data_bits != 0");

endmodule
