/***********************************************************************
        File: comms_tests_sequence.sv
 Description: Tests all ISO/IEC 14443A comms messages
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

package comms_tests_sequence_pkg;

    import std_block_address_pkg::StdBlockAddress;
    import rx_byte_transaction_pkg::RxByteTransaction;

    // virtual because the TB must override several functions/tasks:
    //      do_reset
    //      get_std_i_reply_inf
    //      set_power_input
    //      verify_dut_cid
    virtual class CommsTestsSequence
    #(
        // These must extend QueueTransaction
        type RxTransType,
        type TxTransType,

        // This must be / extend TransactionGenerator
        type TransGenType   = transaction_generator_pkg::TransactionGenerator,

        // These must extend TransactionConverter
        type RxTransConvType,
        type TxTransConvType,

        // This must extend RxDriver
        type RxDriverType,

        // This must extend TxMonitor
        type TxMonitorType
    )
    extends specific_target_sequence_pkg::SpecificTargetSequence
    #(
        .RxTransType        (RxTransType),
        .TxTransType        (TxTransType),
        .TransGenType       (TransGenType),
        .RxTransConvType    (RxTransConvType),
        .TxTransConvType    (TxTransConvType),
        .RxDriverType       (RxDriverType),
        .TxMonitorType      (TxMonitorType)
    );
        typedef enum
        {
            CommsTestsEventCode_SET_DRIVER_ERRORS,
            CommsTestsEventCode_SET_CORRUPT_CRC
        }CommsTestsEventCode;

        typedef enum
        {
            // ISO/IEC 14443-3A messages
            MsgType_REQA,
            MsgType_WUPA,
            MsgType_HLTA,
            MsgType_AC,
            MsgType_nAC,
            MsgType_SELECT,
            MsgType_nSELECT,

            // ISO/IEC 14443-4 messages
            MsgType_RATS,
            MsgType_PPS,
            MsgType_I,
            MsgType_I_CHAINING,
            MsgType_ACK,
            MsgType_NAK,
            MsgType_PARAMETERS,
            MsgType_DESELECT,

            // MISC messages
            MsgType_RANDOM,
            MsgType_ERROR
        } MsgType;

        typedef enum
        {
            NAD_NONE,                   // No NAD
            NAD_PRESENT,                // Use a random NAD
            NAD_RANDOM                  // Randomly has a NAD or not
        } NadType;

        int num_loops_per_test;

        // we change the power input to the 14443_4a module on every send when this is set,
        // and confirm that any replies have the correct value in their CID field
        protected logic randomise_power;

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
                     int                        _reply_timeout,
                     int                        _num_loops_per_test=1000);
            super.new(_picc_uid,
                      _rx_trans_gen,
                      _tx_trans_gen,
                      _rx_trans_conv,
                      _tx_trans_conv,
                      _rx_send_queue,
                      _tx_recv_queue,
                      _rx_driver,
                      _tx_monitor,
                      _reply_timeout);

            num_loops_per_test  = _num_loops_per_test;
            randomise_power     = 1'b1;
        endfunction

        // ====================================================================
        // Pure Virtual functions / tasks
        // must be overriden by a child class
        // ====================================================================
        // defined in SpecificTargetSequence
        //pure virtual task                         do_reset;
        //pure virtual function logic               verify_dut_cid      (logic [3:0] expected);
        pure virtual protected function ByteQueue   get_std_i_reply_inf (logic [7:0] inf [$]);
        pure virtual protected function void        set_power_input(logic [1:0] _power);

        // ====================================================================
        // Callbacks
        // ====================================================================

        // the testbench may override this if it wants to get callbacks from this class
        virtual protected function void comms_tests_callback(CommsTestsEventCode ec, int arg=0);
        endfunction

        // ====================================================================
        // Enable / Disable driver errors / CRC errors
        // ====================================================================

        virtual protected function void set_corrupt_crc(logic en);
            // Tell the TB that we are sending / not sending CRC errors
            comms_tests_callback(CommsTestsEventCode_SET_CORRUPT_CRC, en);

            // disable / enable state tracking in our parent class
            // so it doesn't register a state change incorrectly
            disable_state_tracking = en;

            // get the rx transaction generator to add / stop adding CRC errors
            rx_trans_gen.set_corrupt_crc(en);
        endfunction

        virtual protected function void set_driver_add_error(logic en);
            // Tell the TB that we are sending / not sending errors
            comms_tests_callback(CommsTestsEventCode_SET_DRIVER_ERRORS, en);

            // disable / enable state tracking in our parent class
            // so it doesn't register a state change incorrectly
            disable_state_tracking = en;

            // get the rx transaction generator to add / stop adding errors
            rx_driver.set_add_error(en);
        endfunction

        // ====================================================================
        // CID / NAD / Address helper functions
        // ====================================================================

        virtual protected function logic get_has_nad_from_nad_type(NadType nad_type);
            case (nad_type)
                NAD_NONE:       return 1'b0;
                NAD_PRESENT:    return 1'b1;
                NAD_RANDOM:     return $urandom;
            endcase
        endfunction

        virtual protected function StdBlockAddress get_std_block_address(CidType cid_type, NadType nad_type=NAD_NONE);
            automatic StdBlockAddress res = new ((cid_type != CID_NONE),
                                                 get_cid_from_cid_type(cid_type),
                                                 picc_target.get_power(),
                                                 get_has_nad_from_nad_type(nad_type),
                                                 $urandom);
            return res;
        endfunction

        // ====================================================================
        // Generate INF field for STD I-Blocks and S(PARAMAETERS)
        // ====================================================================

        // This can be overriden to generate valid app messages, but here we just randomise it.
        virtual protected function ByteQueue generate_inf(MsgType msg_type);
            automatic int       num_bytes   = $urandom_range(10);
            automatic ByteQueue res         = '{};
            repeat (num_bytes) begin
                res.push_back($urandom);
            end
            return res;
        endfunction

        // ====================================================================
        // Sending tasks
        // ====================================================================

        // we override this, so we can randomise the power signal
        virtual task send_transaction (RxByteTransaction byte_trans, EventMessageID mid);
            if (randomise_power) begin
                automatic logic [1:0] power = 2'($urandom);
                set_power_input(power);
                picc_target.set_power(power);
            end
            super.send_transaction(byte_trans, mid);
        endtask

        virtual task send_random_non_valid;
            send_transaction(rx_trans_gen.generate_random_non_valid($urandom_range(1, 10)),
                             EventMessageID_RANDOM_NON_VALID);

            handle_error_or_part4_comms_state_change;
        endtask

        // ====================================================================
        // send messages and verify their reply
        // ====================================================================

        virtual function MsgType pick_random_message(logic REQA,                logic WUPA,     logic HLTA,
                                                     logic AC,                  logic nAC,
                                                     logic SELECT,              logic nSELECT,
                                                     logic RATS,                logic PPS,
                                                     logic std_i_block,         logic std_i_block_chaining,
                                                     logic std_r_ack,           logic std_r_nak,
                                                     logic std_s_parameters,    logic std_s_deselect,
                                                     logic random,              logic error);
            automatic MsgType   allowed [$] = '{};
            automatic MsgType   to_send;

            if (REQA) begin
                allowed.push_back(MsgType_REQA);
            end
            if (WUPA) begin
                allowed.push_back(MsgType_WUPA);
            end
            if (HLTA) begin
                allowed.push_back(MsgType_HLTA);
            end
            if (AC) begin
                allowed.push_back(MsgType_AC);
            end
            if (nAC) begin
                allowed.push_back(MsgType_nAC);
            end
            if (SELECT) begin
                allowed.push_back(MsgType_SELECT);
            end
            if (nSELECT) begin
                allowed.push_back(MsgType_nSELECT);
            end
            if (RATS) begin
                allowed.push_back(MsgType_RATS);
            end
            if (PPS) begin
                allowed.push_back(MsgType_PPS);
            end
            if (std_i_block) begin
                allowed.push_back(MsgType_I);
            end
            if (std_i_block_chaining) begin
                allowed.push_back(MsgType_I_CHAINING);
            end
            if (std_r_ack) begin
                allowed.push_back(MsgType_ACK);
            end
            if (std_r_nak) begin
                allowed.push_back(MsgType_NAK);
            end
            if (std_s_parameters) begin
                allowed.push_back(MsgType_PARAMETERS);
            end
            if (std_s_deselect) begin
                allowed.push_back(MsgType_DESELECT);
            end
            if (random) begin
                allowed.push_back(MsgType_RANDOM);
            end
            if (error) begin
                allowed.push_back(MsgType_ERROR);
            end

            std::randomize(to_send) with {to_send inside {allowed};};
            return to_send;
        endfunction

        // If wait_for_reply and expect_reply are set then, then the reply must be as
        // expected for message type. We don't check if we are in the correct state here.
        // So if you're in state idle and you send SELECT, it will try to verify the SAK
        // reply, and fail when it doesn't receive it.
        virtual task send_msg(logic     REQA,               logic   WUPA,   logic   HLTA,
                              logic     AC,                 logic   nAC,
                              logic     SELECT,             logic   nSELECT,
                              logic     RATS,               logic   PPS,
                              logic     std_i_block,        logic   std_i_block_chaining,
                              logic     std_r_ack,          logic   std_r_nak,
                              logic     std_s_parameters,   logic   std_s_deselect,
                              logic     random,             logic   error,
                              CidType   cid_type,           NadType nad_type,
                              logic     wait_for_reply,     logic   expect_reply);

            automatic MsgType           to_send;
            automatic int               level;
            automatic int               uid_bits;
            automatic logic [31:0]      invalid_uid;
            automatic logic             i_block;
            automatic StdBlockAddress   addr;
            automatic logic [7:0]       inf [$] = '{};

            to_send = pick_random_message
            (
                .REQA               (REQA),             .WUPA                   (WUPA),     .HLTA   (HLTA),
                .AC                 (AC),               .nAC                    (nAC),
                .SELECT             (SELECT),           .nSELECT                (nSELECT),
                .RATS               (RATS),             .PPS                    (PPS),
                .std_i_block        (std_i_block),      .std_i_block_chaining   (std_i_block_chaining),
                .std_r_ack          (std_r_ack),        .std_r_nak              (std_r_nak),
                .std_s_parameters   (std_s_parameters), .std_s_deselect         (std_s_deselect),
                .random             (random),           .error                  (error)
            );

            // for nAC / nSELECT we allow any level
            if ((to_send == MsgType_AC) || (to_send == MsgType_SELECT)) begin
                // always use level 0 for AC / SELECT
                // we currently assume the tag is either not in the READY / READY* state
                // or it's in one of those, at level 0
                level       = 0;
            end
            else begin
                // for nAC / nSELECT use whatever level
                level       = $urandom_range(0,2);
            end

            // set the number of bits for SELECT / nSELECT = 32
            // or for AC / nAC != 32
            if ((to_send == MsgType_nSELECT) || (to_send == MsgType_SELECT)) begin
                uid_bits = 32;
            end
            else if ((to_send == MsgType_nAC) && (level == picc_target.get_select_level())) begin
                // AC will always match if the level is the correct and
                // uid_bits is 0, so don't allow 0 bits
                uid_bits    = $urandom_range(1,31);
            end
            else begin
                // AC can use any number of bit
                uid_bits    = $urandom_range(31);
            end

            // invent a uid that definitely won't match for nAC / nSELECT
            if (uid_bits != 0) begin
                if (level != picc_target.get_select_level()) begin
                    // sending not the current level, so the UID can be anything
                    std::randomize(invalid_uid);
                end
                else begin
                    // we are sending a level 0 nSELECT / nAC,
                    // so we have to make sure it doesn't match our actual level 0 uid

                    // can't do std::randomize(invalid_uid) with {invalid_uid[uid_bits-1:0] != uid.get_level(0)[uid_bits-1:0];};
                    // since that has a variable range. so create a mask,
                    // and set the bits we don't care about to 0
                    automatic logic [31:0] mask = '0;
                    for (int i = 0; i < uid_bits; i++) begin
                        mask[i] = 1'b1;
                    end

                    // make sure it doesn't match the current level
                    // (level == picc_target.get_select_level())
                    std::randomize(invalid_uid) with
                    {
                        (invalid_uid & mask) != (picc_target.uid.get_level(level) & mask);
                    };
                end
            end

            // NAD is only permitted for STD I-Blocks
            i_block = (to_send == MsgType_I) || (to_send == MsgType_I_CHAINING);
            addr    = get_std_block_address(cid_type, i_block ? nad_type : NAD_NONE);

            // generate the INF field
            inf     = generate_inf(to_send);

            //$display("sending %s, level %d, uid_bits %d, invalid_uid %x", to_send.name, level, uid_bits, invalid_uid);
            case (to_send)
                MsgType_REQA:       send_reqa;
                MsgType_WUPA:       send_wupa;
                MsgType_HLTA:       send_hlta;
                MsgType_AC:         send_ac(0, uid_bits, picc_target.uid.get_level(0));
                MsgType_nAC:        send_ac(level, uid_bits, invalid_uid);
                MsgType_SELECT:     send_select(0, picc_target.uid.get_level(0));
                MsgType_nSELECT:    send_select(level, invalid_uid);
                MsgType_RATS:       send_rats($urandom, get_cid_from_cid_type(cid_type));
                MsgType_PPS:        send_pps(get_cid_from_cid_type(cid_type), $urandom, 0, 0);
                MsgType_I:          send_std_i_block(addr, 1'b0, picc_target.get_pcd_block_num, inf);
                MsgType_I_CHAINING: send_std_i_block(addr, 1'b1, picc_target.get_pcd_block_num, inf);
                MsgType_ACK:        send_std_r_ack(addr, picc_target.get_pcd_block_num);
                MsgType_NAK:        send_std_r_nak(addr, picc_target.get_pcd_block_num);
                MsgType_PARAMETERS: send_std_s_parameters(addr, inf);
                MsgType_DESELECT:   send_std_s_deselect(addr);
                MsgType_RANDOM:     send_random_non_valid;
                MsgType_ERROR:      send_msg_with_error(cid_type, nad_type);
                default:            $fatal(0, "Message %d (%s) not supported here", to_send, to_send.name);
            endcase

            if (wait_for_reply) begin
                // check the response is as it should be
                if (!expect_reply) begin
                    verify_no_reply;
                end
                else begin
                    case (to_send)
                        MsgType_REQA:       wait_for_and_verify_atqa;
                        MsgType_WUPA:       wait_for_and_verify_atqa;
                        MsgType_HLTA:       verify_no_reply;
                        MsgType_AC:         wait_for_and_verify_ac_reply(uid_bits);
                        MsgType_nAC:        verify_no_reply;
                        MsgType_SELECT:     wait_for_and_verify_sak(picc_target.uid.get_num_levels() == 1);
                        MsgType_nSELECT:    verify_no_reply;
                        MsgType_RATS:       wait_for_and_verify_ats;
                        MsgType_PPS:        wait_for_and_verify_ppsr;
                        MsgType_I:          wait_for_and_verify_std_i_block(addr, get_std_i_reply_inf(inf));
                        MsgType_I_CHAINING: verify_no_reply;
                        MsgType_ACK:        verify_no_reply;
                        MsgType_NAK:        wait_for_and_verify_std_r_ack(addr);
                        MsgType_PARAMETERS: verify_no_reply;
                        MsgType_DESELECT:   wait_for_and_verify_std_s_deselect(addr);
                        MsgType_RANDOM:     verify_no_reply;
                        MsgType_ERROR:      verify_no_reply;
                        default:            $fatal(0, "Message %d (%s) not supported here", to_send, to_send.name);
                    endcase
                end
            end
        endtask

        virtual task send_msg_with_error(CidType cid_type, NadType nad_type);
            // TODO: Add an option of parity errors if rx messages have parity bits?

            // tell the driver to add an error
            set_driver_add_error(1'b1);

            // now send any valid / non-valid message (except the error one, so we don't
            // loop indefinately). don't wait for any reply, we verify no_reply in the caller
            send_msg(.REQA              (1'b1),     .WUPA                   (1'b1), .HLTA   (1'b1),
                     .AC                (1'b1),     .nAC                    (1'b1),
                     .SELECT            (1'b1),     .nSELECT                (1'b1),
                     .RATS              (1'b1),     .PPS                    (1'b1),
                     .std_i_block       (1'b1),     .std_i_block_chaining   (1'b1),
                     .std_r_ack         (1'b1),     .std_r_nak              (1'b1),
                     .std_s_parameters  (1'b1),     .std_s_deselect         (1'b1),
                     .random            (1'b1),     .error                  (1'b0),
                     .cid_type          (cid_type), .nad_type               (nad_type),
                     .wait_for_reply    (1'b0),     .expect_reply           (1'b0));

            // re-enable state tracking
            set_driver_add_error(1'b0);

            handle_error_or_part4_comms_state_change;
        endtask

        virtual task send_init_comms_msg_verify_reply(logic REQA,   logic WUPA, logic HLTA,
                                                      logic AC,     logic nAC,
                                                      logic SELECT, logic nSELECT,
                                                      logic random, logic error);

            // pass through all inputs, disable part4 messages.
            // cid and nad are set to random, for use only with the error case.
            // wait for reply and check it is as expected.
            send_msg(.REQA              (REQA),         .WUPA                   (WUPA),     .HLTA   (HLTA),
                     .AC                (AC),           .nAC                    (nAC),
                     .SELECT            (SELECT),       .nSELECT                (nSELECT),
                     .random            (random),       .error                  (error),
                     .RATS              (1'b0),         .PPS                    (1'b0),
                     .std_i_block       (1'b0),         .std_i_block_chaining   (1'b0),
                     .std_r_ack         (1'b0),         .std_r_nak              (1'b0),
                     .std_s_parameters  (1'b0),         .std_s_deselect         (1'b0),
                     .cid_type          (CID_RANDOM),   .nad_type               (NAD_RANDOM),
                     .wait_for_reply    (1'b1),         .expect_reply           (1'b1));
        endtask

        virtual task send_init_comms_msg_verify_no_reply(logic REQA,    logic WUPA, logic HLTA,
                                                         logic AC,      logic nAC,
                                                         logic SELECT,  logic nSELECT,
                                                         logic random,  logic error);

            // pass through all inputs, disable part4 messages.
            // cid and nad are set to random, for use only with the error case.
            // verify that no reply is received.
            send_msg(.REQA              (REQA),         .WUPA                   (WUPA),     .HLTA   (HLTA),
                     .AC                (AC),           .nAC                    (nAC),
                     .SELECT            (SELECT),       .nSELECT                (nSELECT),
                     .random            (random),       .error                  (error),
                     .RATS              (1'b0),         .PPS                    (1'b0),
                     .std_i_block       (1'b0),         .std_i_block_chaining   (1'b0),
                     .std_r_ack         (1'b0),         .std_r_nak              (1'b0),
                     .std_s_parameters  (1'b0),         .std_s_deselect         (1'b0),
                     .cid_type          (CID_RANDOM),   .nad_type               (NAD_RANDOM),
                     .wait_for_reply    (1'b1),         .expect_reply           (1'b0));
        endtask

        virtual task send_part4_comms_msg_verify_reply(logic    RATS,               logic   PPS,
                                                       logic    std_i_block,        logic   std_i_block_chaining,
                                                       logic    std_r_ack,          logic   std_r_nak,
                                                       logic    std_s_parameters,   logic   std_s_deselect,
                                                       logic    random,             logic   error,
                                                       CidType  cid_type,           NadType nad_type);

            // pass through all inputs, disable part3 messages
            // wait for reply and check it is as expected.
            send_msg(.REQA              (1'b0),             .WUPA                   (1'b0),     .HLTA   (1'b0),
                     .AC                (1'b0),             .nAC                    (1'b0),
                     .SELECT            (1'b0),             .nSELECT                (1'b0),
                     .RATS              (RATS),             .PPS                    (PPS),
                     .std_i_block       (std_i_block),      .std_i_block_chaining   (std_i_block_chaining),
                     .std_r_ack         (std_r_ack),        .std_r_nak              (std_r_nak),
                     .std_s_parameters  (std_s_parameters), .std_s_deselect         (std_s_deselect),
                     .random            (random),           .error                  (error),
                     .cid_type          (cid_type),         .nad_type               (nad_type),
                     .wait_for_reply    (1'b1),             .expect_reply           (1'b1));
        endtask

        virtual task send_part4_comms_msg_verify_no_reply(logic     RATS,               logic   PPS,
                                                          logic     std_i_block,        logic   std_i_block_chaining,
                                                          logic     std_r_ack,          logic   std_r_nak,
                                                          logic     std_s_parameters,   logic   std_s_deselect,
                                                          logic     random,             logic   error,
                                                          CidType   cid_type,           NadType nad_type);

            // pass through all inputs, disable part3 messages
            // verify that no reply is receieved
            send_msg(.REQA              (1'b0),             .WUPA                   (1'b0),     .HLTA   (1'b0),
                     .AC                (1'b0),             .nAC                    (1'b0),
                     .SELECT            (1'b0),             .nSELECT                (1'b0),
                     .RATS              (RATS),             .PPS                    (PPS),
                     .std_i_block       (std_i_block),      .std_i_block_chaining   (std_i_block_chaining),
                     .std_r_ack         (std_r_ack),        .std_r_nak              (std_r_nak),
                     .std_s_parameters  (std_s_parameters), .std_s_deselect         (std_s_deselect),
                     .random            (random),           .error                  (error),
                     .cid_type          (cid_type),         .nad_type               (nad_type),
                     .wait_for_reply    (1'b1),             .expect_reply           (1'b0));
        endtask

        // ====================================================================
        // Tests
        // ====================================================================
        // Note: all send_X functions figure out the expected state transition
        //       and inform the testbench via the specific_target_callback.
        //       the testbench can check the DUT is in the correct state based on that.

        virtual task run_initialisation_state_transition_tests;
            // --------------------------------------------------------------------
            // Test all possible state transititions
            // --------------------------------------------------------------------

            // 1) Start in State_IDLE
            //      REQA + WUPA take us to State_READY and reply ATQA
            //      all others leave us in State_IDLE

            // reqa / wupa -> ready + ATQA
            $display("State_IDLE + REQA/WUPA");
            repeat (num_loops_per_test) begin
                go_to_state_idle;
                send_init_comms_msg_verify_reply(.REQA      (1'b1), .WUPA      (1'b1), .HLTA      (1'b0),
                                                 .AC        (1'b0), .nAC       (1'b0),
                                                 .SELECT    (1'b0), .nSELECT   (1'b0),
                                                 .random    (1'b0), .error     (1'b0));
            end

            // all others -> idle + no reply
            $display("State_IDLE + others");
            repeat (num_loops_per_test) begin
                go_to_state_idle;
                send_init_comms_msg_verify_no_reply(.REQA      (1'b0), .WUPA      (1'b0),  .HLTA      (1'b1),
                                                    .AC        (1'b1), .nAC       (1'b1),
                                                    .SELECT    (1'b1), .nSELECT   (1'b1),
                                                    .random    (1'b1), .error     (1'b1));
            end

            // 2) Start in State_READY
            //      AC leaves us in State_READY
            //      SELECT either takes us to State_ACTIVE or leaves us in State_READY depending on level and UID_SIZE
            //      all others return us to State_IDLE

            // AC -> ready + AC reply
            $display("State_READY + AC");
            repeat (num_loops_per_test) begin
                go_to_state_ready;
                // always level 0 for now. We check AC stuff in the run_initialisation_ac_select_tests() task
                send_ac_verify_reply($urandom_range(31));
            end

            // SELECT - just select the tag (as many levels as are needed)
            // we worry about AC / select stuff more later
            $display("State_READY + SELECT");
            repeat (num_loops_per_test) begin
                go_to_state_ready;
                select_tag;         // this checks the SAKs internally
            end

            // all others -> idle, no reply
            $display("State_READY + others");
            repeat (num_loops_per_test) begin
                go_to_state_ready;
                send_init_comms_msg_verify_no_reply(.REQA      (1'b1), .WUPA      (1'b1), .HLTA      (1'b1),
                                                    .AC        (1'b0), .nAC       (1'b1),
                                                    .SELECT    (1'b0), .nSELECT   (1'b1),
                                                    .random    (1'b1), .error     (1'b1));
            end

            // 3) Start in State_ACTIVE
            //      HLTA takes us to State_HALT, no reply
            //      RATS (part4 message, not tested here) takes us to State_PROTOCOL + reply
            //      Anything else takes us to State_IDLE, no reply

            // HLTA -> halt, no reply
            $display("State_ACTIVE + HLTA");
            repeat (num_loops_per_test) begin
                go_to_state_active;
                send_hlta_verify_no_reply;
            end

            // all others -> idle, no reply
            $display("State_ACTIVE + others");
            repeat (num_loops_per_test) begin
                go_to_state_active;
                send_init_comms_msg_verify_no_reply(.REQA      (1'b1), .WUPA      (1'b1), .HLTA      (1'b0),
                                                    .AC        (1'b1), .nAC       (1'b1),
                                                    .SELECT    (1'b1), .nSELECT   (1'b1),
                                                    .random    (1'b1), .error     (1'b1));
            end

            // 4) Start in State_HALT
            //      WUPA take us to State_READY_STAR and reply ATQA
            //      all others leave us in State_HALT, no reply

            // wupa -> ready* + ATQA
            $display("State_HALT + WUPA");
            repeat (num_loops_per_test) begin
                go_to_state_halt;
                send_wupa_verify_reply;
            end

            // all others -> idle + no reply
            $display("State_HALT + others");
            repeat (num_loops_per_test) begin
                go_to_state_halt;
                send_init_comms_msg_verify_no_reply(.REQA      (1'b1), .WUPA      (1'b0),  .HLTA      (1'b1),
                                                    .AC        (1'b1), .nAC       (1'b1),
                                                    .SELECT    (1'b1), .nSELECT   (1'b1),
                                                    .random    (1'b1), .error     (1'b1));
            end

            // 5) Start in State_READY_STAR
            //      AC leaves us in State_READY_STAR
            //      SELECT either takes us to State_ACTIVE_STAR or leaves us in State_READY_STAR
            //      depending on level and UID_SIZE
            //      all others return us to State_HALT

            // AC -> ready_star + AC reply
            $display("State_READY_STAR + AC");
            repeat (num_loops_per_test) begin
                go_to_state_ready_star;
                // always level 0 for now. We check AC stuff more in the run_initialisation_ac_select_tests() task
                send_ac_verify_reply($urandom_range(31));
            end

            // SELECT - just select the tag (as many levels as are needed)
            // we worry about AC / select stuff more later
            $display("State_READY_STAR + SEL");
            repeat (num_loops_per_test) begin
                go_to_state_ready_star;
                select_tag(); // this checks the SAKs internally
            end

            // all others -> halt, no reply
            $display("State_READY_STAR + others");
            repeat (num_loops_per_test) begin
                go_to_state_ready_star;
                send_init_comms_msg_verify_no_reply(.REQA      (1'b1), .WUPA      (1'b1), .HLTA      (1'b1),
                                                    .AC        (1'b0), .nAC       (1'b1),
                                                    .SELECT    (1'b0), .nSELECT   (1'b1),
                                                    .random    (1'b1), .error     (1'b1));
            end

            // 6) Start in State_ACTIVE_STAR
            //      RATS (part4 message, not tested here) takes us to State_PROTOCOL + reply
            //      Anything else takes us to State_IDLE, no reply

            // all others -> halt, no reply
            $display("State_ACTIVE_STAR + others");
            repeat (num_loops_per_test) begin
                go_to_state_active_star;
                send_init_comms_msg_verify_no_reply(.REQA      (1'b1), .WUPA      (1'b1), .HLTA      (1'b1),
                                                    .AC        (1'b1), .nAC       (1'b1),
                                                    .SELECT    (1'b1), .nSELECT   (1'b1),
                                                    .random    (1'b1), .error     (1'b1));
            end

            // 7) Test the transitions into and out of the PROTOCOL state
            //    This is done by sending RATS and DESELECT messages.
            //    If the DUT doesn't actually handle these messages (initialisation / iso14443_3a)
            //    then the TB should override the send_rats_verify_reply() and
            //    send_std_s_deselect_and_verify_reply() tasks to only send the message
            //    and verify that there has been no reply
            $display("into and out of State_PROTOCOL*");
            repeat (num_loops_per_test) begin
                // check we can get into the PROTOCOL* state by asserting iso14443_4a_rats
                // after sending a message from the ACTIVE / ACTIVE_STAR state.
                go_to_state(1'($urandom) ? State_ACTIVE
                                         : State_ACTIVE_STAR);

                // goes to State_PROTOCOL_PPS_ALLOWED
                send_rats_verify_reply(0, 0);

                // check that there's no reply / state change to any message now
                // goes to State_PROTOCOL_STD_COMMS
                repeat (10) begin
                    send_init_comms_msg_verify_no_reply(.REQA      (1'b1), .WUPA      (1'b1), .HLTA  (1'b1),
                                                        .AC        (1'b1), .nAC       (1'b1),
                                                        .SELECT    (1'b1), .nSELECT   (1'b1),
                                                        .random    (1'b1), .error     (1'b1));
                end

                // exit State_PROTOCOL_STD_COMMS to State_HALT using S(DESELECT)
                send_std_s_deselect_verify_reply(std_block_address_pkg::StdBlockAddress::new_no_cid_no_nad);
            end
        endtask

        virtual task run_initialisation_ac_select_tests;
            // --------------------------------------------------------------------
            // Test AC/SELECT
            // --------------------------------------------------------------------

            // repeat these tests in both the ready state and the ready* state
            automatic State states [$] = '{State_READY, State_READY_STAR};

            foreach (states[i]) begin

                // 1) Test all valid ACs for all levels
                $display("%s + all ACs", states[i].name);
                for (int level = 0; level < picc_target.uid.get_num_levels(); level++) begin
                    for (int uid_bits = 0; uid_bits < 32; uid_bits++) begin
                        // go to the ready/ready* state
                        go_to_state(states[i]);

                        // send previous selects
                        for (int l = 0; l < level; l++) begin
                            // auto sends the correct select
                            send_select_verify_reply;
                        end

                        // send AC with uid_bits
                        send_ac_verify_reply(uid_bits);
                    end
                end

                // 2) Test invalid nACs / nSELECTs with the tag in all levels
                //    we've already tested this with the tag in level 0, but repeat anyway
                $display("%s + nAC/nSELECT", states[i].name);
                for (int level = 0; level < picc_target.uid.get_num_levels(); level++) begin
                    repeat (num_loops_per_test) begin
                        // go to the ready/ready* state
                        go_to_state(states[i]);

                        // send previous selects
                        for (int l = 0; l < level; l++) begin
                            send_select_verify_reply;
                        end

                        // send nAC / nSELECT
                        send_init_comms_msg_verify_no_reply(.REQA      (1'b0), .WUPA      (1'b0), .HLTA      (1'b0),
                                                            .AC        (1'b0), .nAC       (1'b1),
                                                            .SELECT    (1'b0), .nSELECT   (1'b1),
                                                            .random    (1'b0), .error     (1'b0));
                    end
                end

                // 3) test all valid ACs / SELECTs but for the wrong level
                $display("%s + AC/SELECT for wrong level", states[i].name);
                for (int actualLevel = 0; actualLevel < picc_target.uid.get_num_levels(); actualLevel++) begin
                    for (int sendLevel = 0; sendLevel < 3; sendLevel++) begin
                        // don't send correct ACs
                        if (sendLevel == actualLevel) begin
                            continue;
                        end

                        for (int uid_bits = 0; uid_bits <= 32; uid_bits++) begin
                            // go to the ready/ready* state
                            go_to_state(states[i]);

                            // send previous selects
                            for (int l = 0; l < actualLevel; l++) begin
                                send_select_verify_reply;
                            end

                            // send nAC with uid_bits
                            begin
                                automatic logic [31:0] uid;
                                if (sendLevel < picc_target.uid.get_num_levels) begin
                                    uid = picc_target.uid.get_level(sendLevel);
                                end
                                else begin
                                    std::randomize(uid);
                                end
                                send_ac_select(sendLevel, uid_bits, uid);
                                verify_no_reply;
                            end
                        end
                    end
                end

                // 4) send the correct AC/SELECT for this level, but with the level code incorrect
                $display("%s + AC/SELECT with level code incorrect", states[i].name);
                for (int actualLevel = 0; actualLevel < picc_target.uid.get_num_levels(); actualLevel++) begin
                    for (int sendLevel = 0; sendLevel < 3; sendLevel++) begin
                        // don't send correct ACs
                        if (sendLevel == actualLevel) begin
                            continue;
                        end

                        // start with uid_bits == 1, otherwise it's always valid
                        for (int uid_bits = 1; uid_bits <= 32; uid_bits++) begin
                            // go to the ready/ready* state
                            go_to_state(states[i]);

                            // send previous selects
                            for (int l = 0; l < actualLevel; l++) begin
                                send_select_verify_reply;
                            end

                            // send AC with uid_bits, correct data but wrong level
                            send_ac_select(sendLevel, uid_bits, picc_target.uid.get_level(actualLevel));
                            verify_no_reply;
                        end
                    end
                end

                // 5) send SELECT with the last bit wrong.
                //    this makes sure that UID Matching runs for the entire UID
                $display("%s + SELECT with last bit wrong", states[i].name);
                for (int level = 0; level < picc_target.uid.get_num_levels(); level++) begin
                    // go to the ready/ready* state
                    go_to_state(states[i]);

                    // send previous selects
                    for (int l = 0; l < level; l++) begin
                        send_select_verify_reply;
                    end

                    // send SELECT, flipping the last bit
                    // IE. not for us
                    send_select(level, picc_target.uid.get_level(level), 1'b1);
                    verify_no_reply;
                end
            end
        endtask

        virtual task run_initialisation_crc_error_tests;
            // --------------------------------------------------------------------
            // Test CRC errors
            // --------------------------------------------------------------------
            // only two messages use CRCs, HLTA and SELECT
            // CRC fail is counted as a transmission error and should return us to HALT / IDLE

            $display("Testing SELECT with CRC error");
            repeat (num_loops_per_test) begin
                // SELECT is only valid in State_READY or State_READY_STAR
                automatic State states [$] = '{State_READY, State_READY_STAR};
                automatic State start_state;

                std::randomize(start_state) with {start_state inside {states};};
                go_to_state(start_state);

                // start corrupting CRCs
                set_corrupt_crc(1'b1);

                // send the select
                send_select (0, picc_target.uid.get_level(0));

                // stop corrupting CRCs
                set_corrupt_crc(1'b0);

                // note the actual state change
                case (picc_state)
                    State_IDLE:                 register_no_state_change;
                    State_READY:                register_state_change(State_IDLE);
                    State_ACTIVE:               register_state_change(State_IDLE);

                    State_HALT:                 register_no_state_change;
                    State_READY_STAR:           register_state_change(State_HALT);
                    State_ACTIVE_STAR:          register_state_change(State_HALT);

                    State_PROTOCOL_PPS_ALLOWED: register_state_change(State_PROTOCOL_STD_COMMS);
                    State_PROTOCOL_STD_COMMS:   register_no_state_change;
                endcase

                // finally check there was no reply
                verify_no_reply;
            end

            $display("Testing HLTA with CRC error");
            repeat (num_loops_per_test) begin
                // HLTA can be sent from any state other than PROTOCOL
                // (although in READY and IDLE we go to IDLE)
                // It's a bit silly that HLTA requires a CRC.
                // Since it does not respond in either case and
                // CRC fail counts as an error, which always does the same
                // as what a valid HLTA would have done in that case.
                // except in State_ACTIVE where we return to IDLE for an error
                // and go to HALT with a valid HLTA.
                automatic State states [$] = '{State_IDLE, State_READY,      State_ACTIVE,
                                               State_HALT, State_READY_STAR, State_ACTIVE_STAR};
                automatic State start_state;

                std::randomize(start_state) with {start_state inside {states};};
                //$display("starting in state %s", start_state.name);
                go_to_state(start_state);

                // start corrupting CRCs
                set_corrupt_crc(1'b1);

                // send the HLTA
                send_hlta;

                // stop corrupting CRCs
                set_corrupt_crc(1'b0);

                // note the actual state change
                case (picc_state)
                    State_IDLE:                 register_no_state_change;
                    State_READY:                register_state_change(State_IDLE);
                    State_ACTIVE:               register_state_change(State_IDLE);

                    State_HALT:                 register_no_state_change;
                    State_READY_STAR:           register_state_change(State_HALT);
                    State_ACTIVE_STAR:          register_state_change(State_HALT);

                    State_PROTOCOL_PPS_ALLOWED: register_state_change(State_PROTOCOL_STD_COMMS);
                    State_PROTOCOL_STD_COMMS:   register_no_state_change;
                endcase

                // and finally check there was no reply
                verify_no_reply;
            end
        endtask

        virtual task run_initialisation_part4_comms_ignored_tests;
            // for each initialisation state test that any and all part4 messages are ignored
            // In states ACTIVE and ACTIVE_STAR we can't send RATS
            automatic State states[$] =
            '{
                State_IDLE,
                State_READY,
                State_ACTIVE,
                State_HALT,
                State_READY_STAR,
                State_ACTIVE_STAR
            };

            $display("Testing part4 comms messages are ignored");
            foreach (states[i]) begin
                $display("  Testing state: %s", states[i].name);
                repeat (num_loops_per_test) begin
                    automatic logic     allow_rats  = 1'b1;
                    automatic CidType   cid_type    = 1'($urandom) ? CID_RANDOM_WITH_15 : CID_NONE;

                    if ((states[i] == State_ACTIVE) || (states[i] == State_ACTIVE_STAR)) begin
                        allow_rats = 1'b0;
                    end

                    go_to_state(states[i]);

                    send_part4_comms_msg_verify_no_reply(.RATS              (allow_rats),   .PPS                    (1'b1),
                                                         .std_i_block       (1'b1),         .std_i_block_chaining   (1'b1),
                                                         .std_r_ack         (1'b1),         .std_r_nak              (1'b1),
                                                         .std_s_parameters  (1'b1),         .std_s_deselect         (1'b1),
                                                         .random            (1'b0),         .error                  (1'b0),
                                                         .cid_type          (cid_type),     .nad_type               (NAD_RANDOM));
                end
            end
        endtask

        virtual task run_part4_pcd_first_test;
            automatic int old_reply_timeout = reply_timeout;
            $display("Testing Rule 1) The first block shall be sent by the PCD");
            go_to_state_idle;

            // wait longer than normal and check the PICC doesn't transmit anything
            reply_timeout = reply_timeout * 10;
            verify_no_reply;
            reply_timeout = old_reply_timeout;
        endtask

        virtual task run_part4_expect_rats_tests;
            // 1) Test State_EXPECT_RATS + RATS -> ATS
            $display("Testing State_EXPECT_RATS + valid RATS -> ATS");
            repeat (num_loops_per_test) begin
                go_to_state_expect_rats;
                // ISO/IEC 14443-4:2016 section 5.1
                // FSDI D-F is RFU, the PICC should interpret those values as C.
                //                  we currently ignore FSDI, so test all values.
                // CID = 15 is RFU, the PICC shall not respond and shall enter IDLE state
                //                   or HALT state as specified in ISO/IEC 14443-3:2016,
                send_rats_verify_reply($urandom, get_cid_from_cid_type(CID_RANDOM));
            end

            // 2) Test State_EXPECT_RATS + invalid RATS
            $display("Testing State_EXPECT_RATS + invalid RATS");
            repeat (num_loops_per_test) begin
                go_to_state_expect_rats;
                // ISO/IEC 14443-4:2016 section 5.1
                // CID = 15 is RFU, the PICC shall not respond and shall enter IDLE state
                //                   or HALT state as specified in ISO/IEC 14443-3:2016,
                send_rats($urandom, 4'd15);
                verify_no_reply;
            end

            // 3) Test State_EXPECT_RATS + anything else
            $display("Testing State_EXPECT_RATS + others");
            repeat (num_loops_per_test) begin
                go_to_state_expect_rats;

                // send any message other than RATS, send with or without a random CID / NAD
                send_part4_comms_msg_verify_no_reply(.RATS              (1'b0),                 .PPS                    (1'b1),
                                                     .std_i_block       (1'b1),                 .std_i_block_chaining   (1'b1),
                                                     .std_r_ack         (1'b1),                 .std_r_nak              (1'b1),
                                                     .std_s_parameters  (1'b1),                 .std_s_deselect         (1'b1),
                                                     .random            (1'b1),                 .error                  (1'b1),
                                                     .cid_type          (CID_RANDOM_WITH_15),   .nad_type               (NAD_RANDOM));
            end
        endtask

        virtual task run_part4_pps_tests;
            // 1) Test State_PPS_ALLOWED + PPS (with / without P1) -> PPSR
            $display("Testing State_PPS_ALLOWED + valid PPS -> PPSR");
            repeat (num_loops_per_test) begin
                go_to_state_protocol_pps_allowed;
                send_pps_verify_reply(1'($urandom), 0, 0);

                // send a second PPS and check we don't respond
                send_pps(get_cid_from_cid_type(CID_CURRENT), 1'($urandom), 0, 0);
                verify_no_reply;
            end

            // 2) Test State_PPS_ALLOWED + invalid PPS (cid not us) -> no reply
            $display("Testing State_PPS_ALLOWED + invalid PPS (cid not us) -> no reply");
            repeat (num_loops_per_test) begin
                go_to_state_protocol_pps_allowed;
                send_pps(get_cid_from_cid_type(CID_RANDOM_NOT_CURRENT), 1'($urandom), 0, 0);
                verify_no_reply;
                // send a second PPS (to us this time) and check we don't respond
                send_pps(get_cid_from_cid_type(CID_CURRENT), 1'($urandom), 0, 0);
                verify_no_reply;
            end

            // 3) Test State_PPS_ALLOWED + invalid PPS (dividers) -> no reply
            $display("Testing State_PPS_ALLOWED + invalid PPS (dividers) -> no reply");
            repeat (num_loops_per_test) begin
                go_to_state_protocol_pps_allowed;
                send_pps(get_cid_from_cid_type(CID_CURRENT), 1'b1, 2'($urandom_range(1,3)), 2'($urandom_range(1,3)));
                verify_no_reply;

                // send a second PPS (valid this time) and check we don't respond
                send_pps(get_cid_from_cid_type(CID_CURRENT), 1'($urandom), 0, 0);
                verify_no_reply;
            end

            // 4) Test State_PPS_ALLOWED + invalid PPS (crc) -> no reply
            $display("Testing State_PPS_ALLOWED + invalid PPS (crc) -> no reply");
            repeat (num_loops_per_test) begin
                go_to_state_protocol_pps_allowed;

                set_corrupt_crc(1'b1);
                send_pps(get_cid_from_cid_type(CID_CURRENT), 1'($urandom), 0, 0);
                verify_no_reply;
                set_corrupt_crc(1'b0);

                // send a second PPS (valid this time) and check we don't respond
                send_pps(get_cid_from_cid_type(CID_CURRENT), 1'($urandom), 0, 0);
                verify_no_reply;
            end

            // 5) Test State_PPS_ALLOWED + invalid PPS (error) -> no reply
            $display("Testing State_PPS_ALLOWED + invalid PPS (error) -> no reply");
            repeat (num_loops_per_test) begin
                go_to_state_protocol_pps_allowed;
                set_driver_add_error(1'b1);
                send_pps(get_cid_from_cid_type(CID_CURRENT), 1'($urandom), 0, 0);
                set_driver_add_error(1'b0);
                verify_no_reply;

                // send a second PPS (valid this time) and check we don't respond
                send_pps(get_cid_from_cid_type(CID_CURRENT), 1'($urandom), 0, 0);
                verify_no_reply;
            end

            // 6) Test State_PPS_ALLOWED + RATS -> no reply
            $display("Testing State_PPS_ALLOWED + RATS -> no reply");
            repeat (num_loops_per_test) begin: PPSAllowedPlusRATS
                automatic logic [3:0] old_cid;
                go_to_state_protocol_pps_allowed;

                // cache our current CID
                old_cid = picc_target.get_cid;

                // send a RATS any CID (!= 15)
                send_rats ($urandom_range(15), get_cid_from_cid_type(CID_RANDOM));
                verify_no_reply;

                // check that we don't think the CID has changed
                // this is a sanity check on our test code
                ourCIDNotChanged:
                assert (picc_target.get_cid == old_cid) else $error("The sequencer's CID has changed on second RATS");

                // check that the DUT's CID hasn't changed
                void'(verify_dut_cid(old_cid));
            end
        endtask

        virtual task run_part4_std_comms_tests;
            // This test runs multiple times
            // repeat 3 times - go to State_PROTOCOL_PPS_ALLOWED before each test
            //                - go to State_PROTOCOL_STD_COMMS before each test
            //                - go to State_PROTOCOL_STD_COMMS once at the start of the loop

            typedef enum
            {
                TestType_STATE_PPS_ALLOWED_BEFORE_EACH_TEST,
                TestType_STATE_STD_COMMS_BEFORE_EACH_TEST,
                TestType_STATE_STD_COMMS_ONCE
            } TestType;

            automatic TestType tests [$] = '{TestType_STATE_PPS_ALLOWED_BEFORE_EACH_TEST,
                                             TestType_STATE_STD_COMMS_BEFORE_EACH_TEST,
                                             TestType_STATE_STD_COMMS_ONCE};

            foreach (tests[testIdx]) begin
                automatic State state                       = State_PROTOCOL_STD_COMMS;
                automatic logic change_state_before_test    = 1'b1;

                // for each of those tests, we repeat twice more
                //      - PCD assigns random CID (not 0), messages are sent with CID
                //      - PCD assigns CID=0, messages are sent without CID
                automatic CidType cid_types [2]             = '{CID_RANDOM_NOT_ZERO, CID_NONE};

                if (tests[testIdx] == TestType_STATE_PPS_ALLOWED_BEFORE_EACH_TEST) begin
                    state = State_PROTOCOL_PPS_ALLOWED;
                end

                foreach (cid_types[cid_idx]) begin
                    automatic CidType   set_cid_type;
                    automatic CidType   send_cid_type;
                    automatic logic     expect_cid;

                    // when setting CID, use specified CID type
                    set_cid_type    = cid_types[cid_idx];
                    // when sending messages use the current CID if we have one, or CID_NONE if we don't
                    send_cid_type   = (cid_types[cid_idx] == CID_NONE) ? CID_NONE
                                                                       : CID_CURRENT;
                    // do we expect a CID in the reply?
                    expect_cid      = cid_types[cid_idx] != CID_NONE;

                    $display("Running test: %s with cid_type %s", tests[testIdx].name, cid_types[cid_idx].name);

                    // if we are in the TestType_STATE_STD_COMMS_ONCE
                    // then goto State_PROTOCOL_STD_COMMS once here
                    if (tests[testIdx] == TestType_STATE_STD_COMMS_ONCE) begin
                        go_to_state(State_PROTOCOL_STD_COMMS, set_cid_type);
                        change_state_before_test = 1'b0;
                    end

                    // 1) RATS is ignored
                    $display("  Testing RATS is ignored");
                    repeat (num_loops_per_test) begin
                        if (change_state_before_test) begin
                            go_to_state(state, set_cid_type);
                        end

                        // send a RATS any CID (!= 15)
                        send_rats($urandom_range(15), CID_RANDOM);
                        verify_no_reply;
                    end

                    // 2) PPS is ignored (only in State_PROTOCOL_STD_COMMS)
                    if (state == State_PROTOCOL_STD_COMMS) begin
                        $display("  Testing PPS is ignored");
                        repeat (num_loops_per_test) begin
                            if (change_state_before_test) begin
                                go_to_state(state, set_cid_type);
                            end

                            // send a PPS
                            send_pps(get_cid_from_cid_type(send_cid_type), 1'($urandom), 0, 0);
                            verify_no_reply;
                        end
                    end

                    // 3) Test S(PARAMETERS)
                    $display("  Testing S(PARAMETERS)");
                    repeat (num_loops_per_test) begin
                        automatic logic [7:0] inf [$] = generate_inf(MsgType_PARAMETERS);

                        if (change_state_before_test) begin
                            go_to_state(state, set_cid_type);
                        end

                        // send S(PARAMETERS)
                        send_std_s_parameters(get_std_block_address(send_cid_type), inf);
                        verify_no_reply;
                    end

                    // 4) Test S(DESELECT)
                    // note: We don't do this in TestType_STATE_STD_COMMS_ONCE
                    //       as it would cause us to leave State_PROTOCOL_STD_COMMS
                    if (change_state_before_test) begin
                        $display("  Testing S(DESELECT)");
                        repeat (num_loops_per_test) begin
                            go_to_state(state, set_cid_type);

                            // send S(DESELECT)
                            send_std_s_deselect_verify_reply(get_std_block_address(send_cid_type));
                        end
                    end

                    // 5) Test I-blocks with chaining are ignored
                    $display("  Testing I-blocks with chaining");
                    repeat (num_loops_per_test) begin
                        automatic logic [7:0] inf [$] = generate_inf(MsgType_I_CHAINING);

                        if (change_state_before_test) begin
                            go_to_state(state, set_cid_type);
                        end

                        // send I-block witch chaining enabled
                        // we also add a NAD 50% of the time
                        // which should also mean the message is ignored.
                        send_std_i_block(get_std_block_address(send_cid_type, NAD_RANDOM),
                                         1'b1, // chaining
                                         picc_target.get_pcd_block_num(),
                                         inf);
                        verify_no_reply;
                    end

                    // 6) Test I-blocks with NADs are ignored
                    $display("  Testing I-blocks with NADs");
                    repeat (num_loops_per_test) begin
                        automatic logic [7:0] inf [$] = generate_inf(MsgType_I);
                        if (change_state_before_test) begin
                            go_to_state(state, set_cid_type);
                        end

                        // send I-block without chaining but with a NAD
                        send_std_i_block(get_std_block_address(send_cid_type, NAD_PRESENT),
                                         1'b0, // not chaining
                                         picc_target.get_pcd_block_num(),
                                         inf);
                        verify_no_reply;
                    end

                    // 7a) Test valid I-blocks are forwarded to the app and the reply comes through
                    $display("  Testing valid I-blocks");
                    repeat (num_loops_per_test) begin
                        automatic logic [7:0] send_inf  [$] = generate_inf(MsgType_I);
                        automatic logic [7:0] reply_inf [$] = get_std_i_reply_inf(send_inf);

                        if (change_state_before_test) begin
                            go_to_state(state, set_cid_type);
                        end

                        //$display("sending I-block with inf: %p", inf);

                        // send I-block without chaining and no NAD
                        send_std_i_block_verify_reply(get_std_block_address(send_cid_type), send_inf, reply_inf);
                    end

                    // 7b) Test I-blocks with CRC fails
                    $display("  Testing valid I-blocks with CRC fails");
                    repeat (num_loops_per_test) begin
                        automatic logic [7:0] inf [$] = generate_inf(MsgType_I);

                        if (change_state_before_test) begin
                            go_to_state(state, set_cid_type);
                        end

                        // send I-block without chaining and no NAD
                        set_corrupt_crc(1'b1);
                        send_std_i_block(get_std_block_address(send_cid_type),
                                         1'b0,
                                         picc_target.get_pcd_block_num(),
                                         inf);
                        set_corrupt_crc(1'b0);

                        // check there's no reply
                        verify_no_reply;
                    end

                    // 7c) Test I-blocks with errors
                    $display("  Testing valid I-blocks with errors");
                    repeat (num_loops_per_test) begin
                        automatic logic [7:0] inf [$] = generate_inf(MsgType_I);

                        if (change_state_before_test) begin
                            go_to_state(state, set_cid_type);
                        end

                        // send I-block without chaining and no NAD
                        set_driver_add_error(1'b1);
                        send_std_i_block(get_std_block_address(send_cid_type),
                                         1'b0,
                                         picc_target.get_pcd_block_num(),
                                         inf);
                        set_driver_add_error(1'b0);

                        // check there's no reply
                        verify_no_reply;
                    end

                    // 8) Test R(ACK) with current PCD block num are ignored
                    $display("  Testing R(ACK) with current PCD block num");
                    repeat (num_loops_per_test) begin
                        if (change_state_before_test) begin
                            go_to_state(state, set_cid_type);
                        end

                        // ISO/IEC 14443-4:2016 section 7.5.5.3 rule 13) states that
                        // When an R(ACK) block is received, if it's block number is not equal to the
                        // PICC’s current block number and the PICC is in chaining, chaining shall be
                        // continued.
                        // Since we don't support chaining, ACKs with block number != the PICC's
                        // current block number are ignored. check that this is the case here,
                        // as a sanity check of our block_num tracking code.
                        // asserting is hard because Synopsys doesn't like unnamed asserts
                        // and doesn't seem to name loops correctly. So I use a $fatal instead
                        if (picc_target.picc_and_pcd_block_nums_are_equal) begin
                            // the PCD's block num is equal to the PICC's block num.
                            // we want to test when they are not equal
                            $fatal(0, "PCD block num == PICC block num");
                        end
                        send_std_r_ack(get_std_block_address(send_cid_type), picc_target.get_pcd_block_num());
                        verify_no_reply;
                    end

                    // 9) Test R(NAK) with current PCD block num -> R(ACK)
                    $display("  Testing R(NAK) with current PCD block num -> R(ACK)");
                    repeat (num_loops_per_test) begin
                        if (change_state_before_test) begin
                            go_to_state(state, set_cid_type);
                        end

                        // ISO/IEC 14443-4:2016 section 7.5.5.3 rule 12) states that
                        // When an R(NAK) block is received, if it's block number is not equal
                        // to the PICC’s current block number, an R(ACK) block shall be sent.
                        // check that this is the case here as a sanity check of our block_num
                        // tracking code.
                        if (picc_target.picc_and_pcd_block_nums_are_equal) begin
                            // the PCD's block num is equal to the PICC's block num.
                            // we want to test when they are not equal
                            $fatal(0, "PCD block num == PICC block num");
                        end

                        send_std_r_nak_correct_block_num_verify_reply(get_std_block_address(send_cid_type));
                    end

                    // 10) Test R(ACK/NAK) with toggled PCD block num -> resend last
                    $display("  Testing R(ACK/NAK) with toggled PCD block num");
                    repeat (num_loops_per_test) begin
                        automatic MsgType       dummy;
                        automatic logic [7:0]   data        [$];

                        if (change_state_before_test) begin
                            go_to_state(state, set_cid_type);
                        end

                        // first send random (valid message) I-block, R(NAK).
                        // we don't allow S(DESELECT) because that complicates rx_deselect detection
                        // and the appropriate PCD response to not receiving the S(DESELECT) reply
                        // is to resend S(DESELECT).
                        // we don't allow R(ACK) because that doesn't result in a reply
                        send_part4_comms_msg_verify_reply(.RATS             (1'b0),             .PPS                    (1'b0),
                                                          .std_i_block      (1'b1),             .std_i_block_chaining   (1'b0),
                                                          .std_r_ack        (1'b0),             .std_r_nak              (1'b1),
                                                          .std_s_parameters (1'b0),             .std_s_deselect         (1'b0),
                                                          .random           (1'b0),             .error                  (1'b0),
                                                          .cid_type         (send_cid_type),    .nad_type               (NAD_NONE));

                        // toggle the PCD block num (fake not having received the reply)
                        picc_target.toggle_pcd_block_num;

                        // ISO/IEC 14443-4:2016 section 7.5.5.3 rule 11) states that
                        // When an R(ACK) or an R(NAK) block is received, if it's block number is equal
                        // to the PICC's current block number, the last block shall be re-transmitted.
                        // Wheras section 7.5.6.2 b) states:
                        // toggle its block number then send an R(NAK) block and expect to receive
                        // the last I-block from the PICC [rule 11].
                        // So as a sanity check, thest these are the same thing (aka, toggling pcd_block_num
                        // means the pcd's and picc's are equeal
                        if (!picc_target.picc_and_pcd_block_nums_are_equal) begin
                            // The PCD's is not equal to the PICC's block num.
                            // we want to test when they are equal
                            $fatal(0, "PCD block num != PICC block num (in the DUT)");
                        end

                        // send an R(ACK) or R(NAK)
                        // don't randomize the power signal
                        // or this beraks the verify_repeat_last checking
                        randomise_power = 1'b0;

                        // send an ACK or a NAK
                        if (1'($urandom)) begin
                            send_std_r_ack_verify_resend_last(get_std_block_address(send_cid_type));
                        end
                        else begin
                            send_std_r_nak_verify_resend_last(get_std_block_address(send_cid_type));
                        end

                        // go back to randomising the power signal after every transmit
                        randomise_power = 1'b1;
                    end

                    // 11) Test errors (random invalid data, rx_iface.error)
                    $display("  Testing invalid / errors");
                    repeat (num_loops_per_test) begin
                        if (change_state_before_test) begin
                            go_to_state(state, set_cid_type);
                        end

                        // send either a random none-valid msg, or any valid one with a CRC fail / error
                        send_part4_comms_msg_verify_no_reply(.RATS              (1'b0),             .PPS                    (1'b0),
                                                             .std_i_block       (1'b0),             .std_i_block_chaining   (1'b0),
                                                             .std_r_ack         (1'b0),             .std_r_nak              (1'b0),
                                                             .std_s_parameters  (1'b0),             .std_s_deselect         (1'b0),
                                                             .random            (1'b1),             .error                  (1'b1),
                                                             .cid_type          (send_cid_type),    .nad_type               (NAD_NONE));
                    end

                    // 12) Test CRC fail
                    $display("  Testing CRC errors");
                    repeat (num_loops_per_test) begin
                        if (change_state_before_test) begin
                            go_to_state(state, set_cid_type);
                        end

                        set_corrupt_crc(1'b1);
                        // send any message
                        send_part4_comms_msg_verify_no_reply(.RATS              (1'b1),             .PPS                    (1'b1),
                                                             .std_i_block       (1'b1),             .std_i_block_chaining   (1'b1),
                                                             .std_r_ack         (1'b1),             .std_r_nak              (1'b1),
                                                             .std_s_parameters  (1'b1),             .std_s_deselect         (1'b1),
                                                             .random            (1'b1),             .error                  (1'b1),
                                                             .cid_type          (send_cid_type),    .nad_type               (NAD_NONE));
                        set_corrupt_crc(1'b0);
                    end

                    // 13) Test not for us
                    $display("  Testing not for us");
                    repeat (num_loops_per_test) begin
                        if (change_state_before_test) begin
                            go_to_state(state, set_cid_type);
                        end

                        // send any STD block with CID not CURRENT
                        send_part4_comms_msg_verify_no_reply(.RATS              (1'b0),                     .PPS                    (1'b0),
                                                             .std_i_block       (1'b1),                     .std_i_block_chaining   (1'b1),
                                                             .std_r_ack         (1'b1),                     .std_r_nak              (1'b1),
                                                             .std_s_parameters  (1'b1),                     .std_s_deselect         (1'b1),
                                                             .random            (1'b0),                     .error                  (1'b0),
                                                             .cid_type          (CID_RANDOM_NOT_CURRENT),   .nad_type               (NAD_NONE));
                    end

                    // 14) Test no CID (only when set_cid_type != CID_NONE)
                    if (set_cid_type != CID_NONE) begin
                        $display("  Testing no CID");
                        repeat (num_loops_per_test) begin
                            if (change_state_before_test) begin
                                go_to_state(state, set_cid_type);
                            end

                            // send any STD block without a CID
                            send_part4_comms_msg_verify_no_reply(.RATS              (1'b0),     .PPS                    (1'b0),
                                                                 .std_i_block       (1'b1),     .std_i_block_chaining   (1'b1),
                                                                 .std_r_ack         (1'b1),     .std_r_nak              (1'b1),
                                                                 .std_s_parameters  (1'b1),     .std_s_deselect         (1'b1),
                                                                 .random            (1'b0),     .error                  (1'b0),
                                                                 .cid_type          (CID_NONE), .nad_type               (NAD_NONE));
                        end
                    end

                    // 15) PICC presence checks, see ISO/IEC 14443-4:2016 section 7.5.6
                    // 15a)  Method 1 - The PCD may send and empty I-Block and expect to
                    //       receive an I-Block from the PICC.
                    // Note: We don't test this here because we've already tested I-Block
                    //       transmissions work. And while we don't explicitly test empty
                    //       I-Blocks the size of the INF field is random and includes 0 in it's range.

                    // 15b)  Method 2 - Before the first I-block exchange, the PCD may send an
                    //       R(NAK) block (with block number 0) and expect to receive an R(ACK)
                    //       (with block number 1) block from the PICC [rule 12].
                    // Note: We can only do this if change_state_before_test is set, otherwise
                    //       there have been I-Block exchanges already
                    // Note: We do test this here because it explicitly gives block numbers.
                    //       While we have already tested R(NAK) -> R(ACK) as the first messages
                    //       after RATS, this ensures that the block numbers work as expected.
                    if (change_state_before_test) begin
                        $display("  Testing PICC presence check Method 2 (before first I-Block exchange");
                        repeat (num_loops_per_test) begin
                            go_to_state(state, set_cid_type);

                            // send an R(NAK) with block num 0, expect the reply to be
                            // R(ACK) with block num 1.
                            if ((picc_target.get_pcd_block_num() != 0) ||
                                (picc_target.get_picc_block_num() != 1))  begin
                                $fatal(0, "Expecting pcd_block_num 0, picc_block_num 1");
                            end
                            send_std_r_nak_correct_block_num_verify_reply(get_std_block_address(send_cid_type));
                        end
                    end

                    // 15b.i) Method 2 - After the first I-block exchange, the PCD may either
                    //        a) send an R(NAK) block (with current block number) and expect
                    //           to receive an R(ACK) block from the PICC [rule 12].
                    // Note: we don't test this here, we already know that an R(NAK) with the correct
                    //       block number will cause an R(ACK) to be received.

                    // 15b.ii) Method 2 - or
                    //         b) toggle its block number then send an R(NAK) block and expect to
                    //            receive the last I-block from the PICC [rule 11].
                    // Note: again we don't test this here, as we know that this works

                    // 16) Test all initialisation messages are ignored
                    $display("  Testing initialisation comms are ignored");
                    repeat (num_loops_per_test) begin
                        if (change_state_before_test) begin
                            go_to_state(state, set_cid_type);
                        end

                        send_init_comms_msg_verify_no_reply(.REQA      (1'b1), .WUPA      (1'b1),  .HLTA      (1'b1),
                                                            .AC        (1'b1), .nAC       (1'b1),
                                                            .SELECT    (1'b1), .nSELECT   (1'b1),
                                                            .random    (1'b0), .error     (1'b0));
                    end
                end
            end
        endtask

        virtual task run_all_initialisation_tests;
            run_initialisation_state_transition_tests;
            run_initialisation_ac_select_tests;
            run_initialisation_crc_error_tests;
            run_initialisation_part4_comms_ignored_tests;
        endtask

        virtual task run_all_part4_tests;
            run_part4_pcd_first_test;
            run_part4_expect_rats_tests;
            run_part4_pps_tests;
            run_part4_std_comms_tests;

            // 4) ISO/IEC 14443-4:2016 section 7.5.5.1
            // Rule 1) The first block shall be sent by the PCD
            // Tested in run_pcd_first_test

            // Rule 2) When an I-Block with chaining is received, the block shall be acknowledged
            // by an R(ACK) block.
            // The DUT currently does not support chaining. So we don't test this.

            // Rule 3) S-Blocks are only used in pairs. An S(...) request block shall always
            // be followed by an S(...) response block.
            // The DUT does not support S(PARAMETERS) and as per ISO/IEC 14443-4:2016 section 9
            // the DUT remains mute upon receiving S(PARAMETERS).

            // PCD rules 4) - 8) do not apply to us.

            // Rule 9) The PICC is allowed to send an S(WTX) block instead of an I-block or
            // an R(ACK) block.
            // The PICC as of yet does not support S(WTX)

            // Rule 10) When an I-Block not indicating chaining is received, the block shall
            // be acknowledged with an I-Block.
            // This is tested in run_std_comms_tests, #7a
            // Note: If the I-Block received is empty then the mandatory I-Block sent can
            //       either be empty or can contain application specific information.

            // Rule 11) When an R(ACK) or an R(NAK) block is received, if it's block number is equal
            // to the PICC's current block number, the last block shall be re-transmitted.
            // This is tested in run_std_comms_tests, #10

            // Rule 12) When an R(NAK) block is received, if it's block number is not equal to the
            // PICC’s current block number, an R(ACK) block shall be sent.
            // This is tested in run_std_comms_tests, #9, and #15

            // Rule 13) When an R(ACK) block is received, if it's block number is not equal to the
            // PICC’s current block number and the PICC is in chaining, chaining shall be continued.
            // The DUT doesn't support chaining, so R(ACKs) with the PICC's current block number are
            // ignored
        endtask

    endclass

endpackage
