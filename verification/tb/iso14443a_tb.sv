/***********************************************************************
        File: iso14443a_tb.sv
 Description: Testbench for the iso14443a module.
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

module iso14443a_tb
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

    import std_block_address_pkg::StdBlockAddress;

    function ISO14443A_pkg::UIDSize get_uid_size (int code);
        return (code == 0) ? ISO14443A_pkg::UIDSize_SINGLE :
               (code == 1) ? ISO14443A_pkg::UIDSize_DOUBLE :
                             ISO14443A_pkg::UIDSize_TRIPLE;
    endfunction

    // --------------------------------------------------------------
    // Timing
    // --------------------------------------------------------------

    // We don't know what the actual clock frequency the PCD will use. To be in spec
    // it has to be 13.56 MHz +/- 7KHz. For the FDT timing adjust we must use the MAX
    // possible period, and so the min possible frequency
    localparam real MIN_CLOCK_FREQ_HZ   = 13560000.0 - 7000.0;
    localparam real MAX_CLOCK_PERIOD_PS = 1000000000000.0 / MIN_CLOCK_FREQ_HZ;

    // this was measured in simulation using the above values.
    // Since the PICC clock can be in phase or 180 degrees out of phase from the PCD clock
    // I picked the minimum value here, as laid out in the comments in iso14443a.sv and fdt.sv
    // in reguards to the FDT_TIMING_ADJUST parameter
    localparam real PCD_PAUSE_N_TO_SYNCHRONISED_PS  = 405603.0;
    localparam real LM_OUT_TO_MODULATION_EDGE_PS    = 0.0;  // we don't yet simulate any delays on the output
    localparam int  FDT_TIMING_ADJUST               = $rtoi((PCD_PAUSE_N_TO_SYNCHRONISED_PS +
                                                             LM_OUT_TO_MODULATION_EDGE_PS) /
                                                            MAX_CLOCK_PERIOD_PS);

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

    logic [1:0]                 power;
    logic                       pause_n_synchronised;
    logic                       lm_out;

    rx_interface #(.BY_BYTE(1)) app_rx_iface (.*);
    tx_interface #(.BY_BYTE(1)) app_tx_iface (.*);
    logic                       app_resend_last;        // output

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    iso14443a
    #(
        .UID_SIZE           (UID_SIZE),
        .UID_INPUT_BITS     (UID_INPUT_BITS),
        .UID_FIXED          (UID_FIXED),
        .FDT_TIMING_ADJUST  (FDT_TIMING_ADJUST)
    )
    dut (.*);

    // For state checking
    ISO14443A_pkg::InitialisationState initState;
    assign initState = ISO14443A_pkg::InitialisationState'(dut.part3.initialisation_inst.state);

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
    // The analogue sim
    // --------------------------------------------------------------
    // this contains the PCD clock source, PICC clk recovery,
    // pause_n detector and the PCDPauseNDriver.

    localparam real CLOCK_FREQ_HZ       = 13560000.0;    // 13.56MHz
    localparam real CLOCK_PERIOD_PS     = 1000000000000.0 / CLOCK_FREQ_HZ;
    logic pcd_pause_n;
    analogue_sim
    #(
        .CLOCK_FREQ_HZ          (int'(CLOCK_FREQ_HZ))
    )
    analogue_sim_inst
    (
        .rst_n                  (rst_n),
        .picc_clk               (clk),
        .pcd_pause_n            (pcd_pause_n),          // used for FDT validation
        .pause_n_async          (),
        .pause_n_synchronised   (pause_n_synchronised)  // goes to the DUT
    );

    // --------------------------------------------------------------
    // The driver / queue / etc... for the pause_n_synchronised input
    // --------------------------------------------------------------

    // driver, note the actual driver is in the analogue_sim above
    typedef pcd_pause_n_driver_pkg::PCDPauseNDriver                             RxDriverType;

    // Rx Transactions
    typedef pcd_pause_n_transaction_pkg::PCDPauseNTransaction                   RxTransType;
    typedef rx_transaction_converter_pkg::RxByteToPCDPauseNTransactionConverter RxTransConvType;

    // the send queue
    typedef RxTransType                                                     RxTransQueueType [$];
    typedef wrapper_pkg::Wrapper #(.Type(RxTransQueueType))                 RxQueueWrapperType;
    RxQueueWrapperType                                                      rx_send_queue;

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
    AppTxTransType                                                          app_tx_send_queue [$];

    // --------------------------------------------------------------
    // The monitor for the lm_out (load modulator) signal
    // --------------------------------------------------------------

    // monitor (produces TxBitTransactions)
    typedef load_modulator_monitor_pkg::LoadModulatorMonitor                TxMonitorType;
    TxMonitorType                                                           tx_monitor;

    // Tx Transactions
    typedef tx_bit_transaction_pkg::TxBitTransaction                        TxTransType;
    typedef tx_transaction_converter_pkg::TxByteToBitTransactionConverter   TxTransConvType;

    // and the recv_queue
    typedef TxTransType                                                     TxTransQueueType [$];
    typedef wrapper_pkg::Wrapper #(.Type(TxTransQueueType))                 TxQueueWrapperType;
    TxQueueWrapperType                                                      tx_recv_queue;

    // interface
    load_modulator_iface                                                    lm_iface (.*);
    assign lm_iface.lm = lm_out;

    // --------------------------------------------------------------
    // FDT verification
    // --------------------------------------------------------------

    // Timings, from ISO/IEC 14443-3:2016 section 6.2.1.1
    localparam int FDT_LAST_BIT_0 = 1172;
    localparam int FDT_LAST_BIT_1 = 1236;

    logic last_rx_bit;
    assign last_rx_bit = dut.part3.framing_inst.last_rx_bit;

    // measure the time between the rising edge of pcd_pause_n
    // and the rising edge of data_valid

    // this is a time in ps (`timescale)
    longint lastPCDPauseRiseTime;

    always_ff @(posedge pcd_pause_n) lastPCDPauseRiseTime <= $time;

    initial begin: fdtVerificationBlock
        forever begin: foreverLoop
            automatic longint diff;
            automatic longint expected;

            // wait for the start of the next Rx frame
            // this ensure we don't check the fdt time on any lm_out pulses other than the first
            @(posedge pcd_pause_n) begin end

            // wait for the start of the reply
            // it doesn't matter if there was no reply to a message, we just get here on the next
            // actual reply. lastPCDPauseRise has been updated for the last rise of the last rx message
            @(posedge lm_out) begin end

            diff        = $time - lastPCDPauseRiseTime;
            expected    = CLOCK_PERIOD_PS * (last_rx_bit ? FDT_LAST_BIT_1 : FDT_LAST_BIT_0);

            // ISO/IEC 14443-3:2016 section 6.2.1.1 requires that the PICC ensures a FDT of
            // the between the value calculated above (expected) and that value + 0.4us.
            // We test here that it is between the expected value and that value + 0.1us.
            // This testbench finds that the actual value is between half a tick and a full tick
            // after the calculated expected value. Which is as expected given that the picc's clock
            // and the pcd clock can be 180 degrees out of phase.

            fdtTime: assert ((diff > expected) &&
                             (diff < (expected + (100 * 1000))))
                else $error("Tx started at %d ps, lastPCDPauseRiseTime %d ps, diff %d, expected %d",
                            $time, lastPCDPauseRiseTime, diff, expected);
        end
    end

    // ----------------------------------------------------------------
    // Extend CommsTestsSequence to do TB specific stuff
    // ----------------------------------------------------------------

    logic expect_app_resend_last;

    class ISO14443a_TbSequence
    extends comms_tests_sequence_pkg::CommsTestsSequence
    #(
        .RxTransType        (RxTransType),
        .TxTransType        (TxTransType),
        .RxTransConvType    (RxTransConvType),
        .TxTransConvType    (TxTransConvType),
        .RxDriverType       (RxDriverType),
        .TxMonitorType      (TxMonitorType)
    );
        // we need to know if the last sent message was a valid STD I-Block for the DUT.
        // Then if an R(ACK/NAK) is sent with the wronge block number we can verify app_resend_last
        // and actually resend the last reply from the app.
        logic       last_sent_was_valid_std_i_block;

        // To be able to resend the last app response, we need to cache what it was
        logic [7:0] app_last_sent_inf [$];

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
                      100);                 // TODO: Run optimised builds and test with more than 100 loops per test

            last_sent_was_valid_std_i_block = 1'b0;
            app_last_sent_inf               = '{};
        endfunction

        virtual task do_reset;
            rst_n <= 1'b0;
            repeat (5) @(posedge clk) begin end
            rst_n <= 1'b1;
            repeat (5) @(posedge clk) begin end
        endtask

        function void sequence_callback(EventCode ec, int arg=0);
            // argument is an EventMessageID
            automatic EventMessageID mid = EventMessageID'(arg);
            //$display("%s %s", ec.name, mid.name);

            case (ec)
                EventCode_SENDING:  begin
                end
                EventCode_SENT: begin: ecSent
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

        function void check_state (State state);
            case (state)
                State_IDLE:                 isIdle:         assert ((initState == ISO14443A_pkg::InitialisationState_IDLE)      && !dut.part3.initialisation_inst.state_star)   else $error("DUT not in correct state expected State_IDLE, 0 got %s, %b",                               initState.name, dut.part3.initialisation_inst.state_star);
                State_READY:                isReady:        assert ((initState == ISO14443A_pkg::InitialisationState_READY)     && !dut.part3.initialisation_inst.state_star)   else $error("DUT not in correct state expected State_READY, 0 got %s, %b",                              initState.name, dut.part3.initialisation_inst.state_star);
                State_ACTIVE:               isActive:       assert ((initState == ISO14443A_pkg::InitialisationState_ACTIVE)    && !dut.part3.initialisation_inst.state_star)   else $error("DUT not in correct state expected State_ACTIVE, 0 got %s, %b",                             initState.name, dut.part3.initialisation_inst.state_star);
                State_HALT:                 isHalt:         assert ((initState == ISO14443A_pkg::InitialisationState_IDLE)      && dut.part3.initialisation_inst.state_star)    else $error("DUT not in correct state expected State_IDLE, 1 got %s, %b",                               initState.name, dut.part3.initialisation_inst.state_star);
                State_READY_STAR:           isReadyStar:    assert ((initState == ISO14443A_pkg::InitialisationState_READY)     && dut.part3.initialisation_inst.state_star)    else $error("DUT not in correct state expected State_READY, 1 got %s, %b",                              initState.name, dut.part3.initialisation_inst.state_star);
                State_ACTIVE_STAR:          isActiveStar:   assert ((initState == ISO14443A_pkg::InitialisationState_ACTIVE)    && dut.part3.initialisation_inst.state_star)    else $error("DUT not in correct state expected State_ACTIVE, 1 got %s, %b",                             initState.name, dut.part3.initialisation_inst.state_star);
                State_PROTOCOL_PPS_ALLOWED: isProtocol1:    assert ((initState == ISO14443A_pkg::InitialisationState_PROTOCOL)  && dut.part4.allow_pps)                         else $error("DUT not in correct state expected State_PROTOCOL_PPS_ALLOWED, got %s, %b, allow_pps %b",   initState.name, dut.part3.initialisation_inst.state_star, dut.part4.allow_pps);
                State_PROTOCOL_STD_COMMS:   isProtocol2:    assert ((initState == ISO14443A_pkg::InitialisationState_PROTOCOL)  && !dut.part4.allow_pps)                        else $error("DUT not in correct state expected State_PROTOCOL_STD_COMMS, got %s, %b, allow_pps %b",     initState.name, dut.part3.initialisation_inst.state_star, dut.part4.allow_pps);
            endcase
        endfunction

        function void comms_tests_callback(CommsTestsEventCode ec, int arg=0);
            case (ec)
                CommsTestsEventCode_SET_CORRUPT_CRC: begin
                end
                CommsTestsEventCode_SET_DRIVER_ERRORS: begin
                end
                default: begin
                    $error("Unknown event code %s", ec.name);
                end
            endcase
        endfunction

        // override send_std_i_block, and verify that the inf field + CRC are forwarded to the app
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
                else if (rx_trans_gen.get_corrupt_crc) begin
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
            assert(dut.part4.our_cid == expected) else $error("DUT's CID is %d expected %d", dut.part4.our_cid, expected);
            return dut.part4.our_cid == expected;
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

    ISO14443a_TbSequence seq;

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin
        automatic transaction_generator_pkg::TransactionGenerator   rx_trans_gen;
        automatic transaction_generator_pkg::TransactionGenerator   tx_trans_gen;
        automatic RxTransConvType                                   rx_trans_conv;
        automatic TxTransConvType                                   tx_trans_conv;
        automatic int                                               reply_timeout;

        power                   = 2'b00;
        expect_app_resend_last  = 1'b0;

        // TODO: randomise some settings:
        //      CLOCK_STARTS/STOPS_AFTER_PS
        //      PAUSE_N_ASSERTS/DEASSERTS_AFTER_PS
        //      pause ticks
        //      clock speed
        //      ...?

        analogue_sim_inst.init(512);    // inits the RxDriver

        app_rx_monitor      = new(app_rx_iface);
        tx_monitor          = new(lm_iface);

        // each byte is 8 bits + parity, 1 bit every 128 ticks -> 1152 ticks, use 2048
        // additionally the fdt timer can take up to 1236 ticks (- FDT_TIMING_ADJUST)
        // so first req can take up to 2388 ticks, use 4096.
        // Using overly large timeouts is fine, as it's something we only epect in error cases.
        app_tx_driver       = new(app_tx_iface, 0, 2048, 4096);

        rx_send_queue       = new('{});
        tx_recv_queue       = new('{});
        // app_tx_send_queue and app_rx_recv_queue are just queues and don't use the wrapper class
        app_rx_recv_queue   = '{};
        app_tx_send_queue   = '{};

        rx_trans_gen        = new(1'b1);    // Rx messages must have CRCs applied
        tx_trans_gen        = new(1'b1);    // Tx messages will have CRCs applied

        rx_trans_conv       = new(1'b1);    // Rx messages must have parity bits
        tx_trans_conv       = new(1'b1);    // Tx messages will have parity bits

        picc_uid            = new('x);

        // longest reply is a STD I-Block reply (2 bytes header, 10 bytes INF, 2 bytes CRC)
        // = 14 bytes, each byte has 8 bits + parity -> 126 bits.
        // there are 128 ticks in a bit, so 16,128 ticks
        // then the FDT takes 1236 ticks to fire (in the worst case)
        // so 17,364 ticks total. Use 18,000 ticks
        // TODO: if we reduce STD I-Block replies to a max of 3 bytes of INF, we can roughly half this
        //       does that give us a decent speedup?
        reply_timeout   = 18000;
        seq             = new(picc_uid,
                              rx_trans_gen,
                              tx_trans_gen,
                              rx_trans_conv,
                              tx_trans_conv,
                              rx_send_queue,
                              tx_recv_queue,
                              analogue_sim_inst.driver,
                              tx_monitor,
                              reply_timeout);

        analogue_sim_inst.start (rx_send_queue.data);
        app_rx_monitor.start    (app_rx_recv_queue);
        tx_monitor.start        (tx_recv_queue.data);
        app_tx_driver.start     (app_tx_send_queue);

        // repeat 10 times with different UIDs
        repeat (10) begin
            // TODO: Add a parameter to let me instead test all possible variable_uid values

            // randomise the variable part of the UID
            picc_uid.randomize;
            full_uid = picc_uid.get_uid;
            $display("NOTE: New UID: %s", picc_uid.to_string);
            seq.do_reset;

            // Run the tests
            seq.run_all_initialisation_tests();
            seq.run_all_part4_tests();
        end

        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

    // check app_resend_last only asserts when expected
    appResendLastOnlyWhenExpected:
    assert property (
        @(posedge clk)
        $rose(app_resend_last) |-> expect_app_resend_last)
        else $error("app_resend_last asserted when not expected");

endmodule
