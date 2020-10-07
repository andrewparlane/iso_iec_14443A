/***********************************************************************
        File: specific_target_sequence.sv
 Description: Comms designed to talk to a PICC with a specific UID
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

package specific_target_sequence_pkg;

    import std_block_address_pkg::StdBlockAddress;
    import tx_byte_transaction_pkg::TxByteTransaction;

    // This class provides functions / tasks to target a particular tag
    // hence it contains the tag's UID and CID.

    // It attempts to keep track of the PICC's state, but the user can confuse it by
    // calling specific functions of the parent class. Such as send_transaction().
    // It also only tracks the expected state. If the module does not respond as expected
    // then this will not be accurate.

    // virtual because the TB must override several functions/tasks:
    //      do_reset
    //      verify_dut_cid
    virtual class SpecificTargetSequence
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
    extends sequence_pkg::Sequence
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
            // See ISO/IEC 14443-3:2016 section 6.3 PICC states

            //State_POWER_OFF,          // we don't use this, because if we are powered on
                                        // then there's an RF field, or it's just disabled
                                        // and we're about to power off
            State_IDLE,
            State_READY,
            State_ACTIVE,

            State_HALT,                 // the initialisation module doesn't have these states
            State_READY_STAR,           // it uses their non-star equivalent and has a separate
            State_ACTIVE_STAR,          // state_star signal.

            State_PROTOCOL_PPS_ALLOWED, // State_PROTOCOL is split into 2 sub states, dictated
            State_PROTOCOL_STD_COMMS    // by ISO/IEC 14443-4. Although they are not explicitly
                                        // stated as separate states it is helpful to make the
                                        // distinction here for testing.
        } State;

        // for use with callback
        typedef enum
        {
            SpecificTargetEventCode_ENTERED_STATE,
            SpecificTargetEventCode_REMAINING_IN_STATE
        } SpecificTargetEventCode;

        typedef enum
        {
            CID_NONE,                   // don't send a CID,    RATS uses CID=0
            CID_15,                     // Use CID=15 (RFU)
            CID_CURRENT,                // use the current CID
            CID_RANDOM,                 // use any CID (0-14)
            CID_RANDOM_NOT_ZERO,        // used for CID assignment, as CID=0 has special conotations
            CID_RANDOM_NOT_CURRENT,     // use any other CID
            CID_RANDOM_WITH_15          // use any CID (0-15)
        } CidType;

        // Info about the target
        target_pkg::Target  picc_target;

        // The target's current state.
        State               picc_state;

        // a flag to disable changing state / reporting state changes
        // can be used by child classes when they want to send a valid message
        // that the PICC won't respond as normal to. For example a REQA with an error,
        // or a SELECT with a CRC error.
        logic               disable_state_tracking;

        // Last message received from the PICC
        TxTransType         last_reply;

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

            super.new(_rx_trans_gen,
                      _tx_trans_gen,
                      _rx_trans_conv,
                      _tx_trans_conv,
                      _rx_send_queue,
                      _tx_recv_queue,
                      _rx_driver,
                      _tx_monitor,
                      _reply_timeout);

            picc_target             = new(_picc_uid);
            disable_state_tracking  = 1'b0;
        endfunction

        // ====================================================================
        // Pure Virtual functions / tasks
        // must be overriden by a child class
        // ====================================================================
        pure virtual task                do_reset;
        pure virtual function logic      verify_dut_cid      (logic [3:0] expected);

        // ====================================================================
        // Callbacks
        // ====================================================================

        // the testbench may override this if it wants to get callbacks from this class
        virtual protected function void specific_target_callback(SpecificTargetEventCode ec, int arg=0);
        endfunction

        // this is just a wrapper around specific_target_callback, for EventCodes that use State
        // as the argument
        virtual protected function void specific_target_callback_state(SpecificTargetEventCode ec, State s);
            specific_target_callback(ec, int'(s));
        endfunction

        // ====================================================================
        // CID / NAD / Address helper functions
        // ====================================================================

        virtual protected function logic [3:0] get_cid_from_cid_type(CidType cid_type);
            logic [3:0] cid;

            case (cid_type)
                CID_NONE:                   cid = 4'd0;
                CID_15:                     cid = 4'd15;
                CID_CURRENT:                cid = picc_target.get_cid;
                CID_RANDOM:                 cid = 4'($urandom_range(0, 14));
                CID_RANDOM_NOT_ZERO:        cid = 4'($urandom_range(1, 14));
                CID_RANDOM_NOT_CURRENT:     std::randomize(cid) with {cid != picc_target.get_cid;};
                CID_RANDOM_WITH_15:         cid = 4'($urandom_range(0, 15));
                default:                    $error("cid_type %s (%d) not supported", cid_type.name, cid_type);
            endcase

            return cid;
        endfunction

        // ====================================================================
        // Sending tasks
        // ====================================================================
        // There are overriden from Sequence and add in state tracking
        // Note that ISO/IEC 14443-4:2016 section 5.6.2.2 (.b and .c) says that
        // ANY message received including errors in State_PROTOCOL_PPS_ALLOWED
        // causes the PICC to stop responding to PPS messages. AKA we transition to
        // State_PROTOCOL_STD_COMMS reguardless of what message was sent

        virtual task send_reqa;
            super.send_reqa;

            // expected state change?
            case (picc_state)
                State_IDLE:                 register_state_change(State_READY);
                State_READY:                register_state_change(State_IDLE);
                State_ACTIVE:               register_state_change(State_IDLE);

                State_HALT:                 register_no_state_change;
                State_READY_STAR:           register_state_change(State_HALT);
                State_ACTIVE_STAR:          register_state_change(State_HALT);

                State_PROTOCOL_PPS_ALLOWED: register_state_change(State_PROTOCOL_STD_COMMS);
                State_PROTOCOL_STD_COMMS:   register_no_state_change;
                default:                    $fatal(0, "States %s not handled here", picc_state.name);
            endcase

            // assuming we went to the Ready / Ready_STAR state reset the select_level
            picc_target.set_select_level(0);
        endtask

        virtual task send_wupa;
            super.send_wupa;

            // expected state change?
            case (picc_state)
                State_IDLE:                 register_state_change(State_READY);
                State_READY:                register_state_change(State_IDLE);
                State_ACTIVE:               register_state_change(State_IDLE);

                State_HALT:                 register_state_change(State_READY_STAR);
                State_READY_STAR:           register_state_change(State_HALT);
                State_ACTIVE_STAR:          register_state_change(State_HALT);

                State_PROTOCOL_PPS_ALLOWED: register_state_change(State_PROTOCOL_STD_COMMS);
                State_PROTOCOL_STD_COMMS:   register_no_state_change;
                default:                    $fatal(0, "States %s not handled here", picc_state.name);
            endcase

            // assuming we went to the Ready / Ready_STAR state reset the select_level
            picc_target.set_select_level(0);
        endtask

        virtual task send_hlta;
            super.send_hlta;

            // expected state change?
            case (picc_state)
                State_IDLE:                 register_no_state_change;
                State_READY:                register_state_change(State_IDLE);
                State_ACTIVE:               register_state_change(State_HALT);

                State_HALT:                 register_no_state_change;
                State_READY_STAR:           register_state_change(State_HALT);
                State_ACTIVE_STAR:          register_state_change(State_HALT);

                State_PROTOCOL_PPS_ALLOWED: register_state_change(State_PROTOCOL_STD_COMMS);
                State_PROTOCOL_STD_COMMS:   register_no_state_change;
                default:                    $fatal(0, "States %s not handled here", picc_state.name);
            endcase
        endtask

        virtual task send_ac_select(int level, int uid_bits, logic [31:0] uid, logic toggle_last_bcc_bit=1'b0);
            automatic logic is_select   = (uid_bits == 32);  // else AC
            automatic logic is_valid    = 1'b0;

            if ((level == picc_target.get_select_level()) &&
                picc_target.uid.compare(level, uid_bits, uid) &&
                !toggle_last_bcc_bit) begin
                // it's for our tag
                is_valid = 1'b1;
            end

            super.send_ac_select(level, uid_bits, uid, toggle_last_bcc_bit);

            // expected state change?
            case (picc_state)
                State_IDLE:                 register_no_state_change;
                State_ACTIVE:               register_state_change(State_IDLE);

                State_HALT:                 register_no_state_change;
                State_ACTIVE_STAR:          register_state_change(State_HALT);

                State_PROTOCOL_PPS_ALLOWED: register_state_change(State_PROTOCOL_STD_COMMS);
                State_PROTOCOL_STD_COMMS:   register_no_state_change;

                // we only deal with AC / SELECT in the Ready / Ready_STAR states
                State_READY, State_READY_STAR:  begin
                    if (!is_valid) begin
                        register_state_change((picc_state == State_READY) ? State_IDLE : State_HALT);
                    end
                    else if (is_select) begin
                        if (level == (picc_target.uid.get_num_levels() - 1)) begin
                            // final level, move to ACTIVE / ACTIVE_STAR
                            register_state_change((picc_state == State_READY) ? State_ACTIVE
                                                                              : State_ACTIVE_STAR);
                        end
                        else begin
                            // more to go, remain in READY / READY_STAR
                            register_no_state_change;
                            picc_target.set_select_level(picc_target.get_select_level+1);
                        end
                    end
                    else begin
                        // remain in the READY / Ready_STAR
                        register_no_state_change;
                    end
                end

                default:                    $fatal(0, "States %s not handled here", picc_state.name);
            endcase
        endtask

        virtual task send_rats(logic [3:0] fsdi, logic [3:0] cid);
            // a RATS with a CID == 15 is an error
            automatic logic [3:0]   old_cid     = picc_target.get_cid;
            automatic logic         is_valid;

            is_valid = (cid != 15) &&
                       !rx_trans_gen.get_corrupt_crc &&
                       !rx_driver.get_add_error;

            super.send_rats(fsdi, cid);

            // expected state change?
            case (picc_state)
                State_IDLE:                 register_no_state_change;
                State_READY:                register_state_change(State_IDLE);

                State_HALT:                 register_no_state_change;
                State_READY_STAR:           register_state_change(State_HALT);

                State_ACTIVE, State_ACTIVE_STAR: begin
                    if (is_valid) begin
                        register_state_change(State_PROTOCOL_PPS_ALLOWED);

                        // check that the new CID has been accepted
                        void'(verify_dut_cid(cid));

                        // Set the target's CID info, snce this is only used to test our IP core
                        // and we always support CIDs, we set the has_cid flag to true and ignore
                        // what the ATS says (the verify_ats function confirms the ATS is as expected).
                        picc_target.set_cid(1'b1, cid);

                        // Initialise the block nums
                        picc_target.initialise_block_nums;
                    end
                    else begin
                        register_state_change((picc_state == State_ACTIVE) ? State_IDLE : State_HALT);
                    end
                end

                State_PROTOCOL_PPS_ALLOWED: begin
                    register_state_change(State_PROTOCOL_STD_COMMS);
                    // confirm the CID hasn't changed
                    void'(verify_dut_cid(old_cid));
                end
                State_PROTOCOL_STD_COMMS:   begin
                    register_no_state_change;
                    // confirm the CID hasn't changed
                    void'(verify_dut_cid(old_cid));
                end

                default:                    $fatal(0, "States %s not handled here", picc_state.name);
            endcase
        endtask

        virtual task send_pps(logic [3:0] cid, logic p1_present, logic [1:0] dsi, logic [1:0] dri);
            super.send_pps(cid, p1_present, dsi, dri);

            handle_error_or_part4_comms_state_change;
        endtask

        virtual task send_std_i_block(StdBlockAddress addr, logic chaining, logic block_num, logic [7:0] inf [$]);
            super.send_std_i_block(addr, chaining, block_num, inf);

            handle_error_or_part4_comms_state_change;

            // ISO/IEC 14443-4:2016 section 7.5.4.2, Rule D
            // When an I-block is received, the PICC shall toggle its block number before sending a block.
            if (picc_target.is_for_us(addr) && !chaining &&
                !rx_driver.get_add_error    && !rx_trans_gen.get_corrupt_crc) begin
                picc_target.toggle_picc_block_num;
            end
        endtask

        virtual task send_std_r_ack(StdBlockAddress addr, logic block_num);
            super.send_std_r_ack(addr, block_num);

            handle_error_or_part4_comms_state_change;

            // We don't support chaining, so the PCD should never send an R(ACK) with block_num
            // not equal to the PICC's block num, thus we do not follow this rule ATM.

            // ISO/IEC 14443-4:2016 section 7.5.4.2, Rule E
            // When an R(ACK) block with a block number not equal to the current PlCC’s block number
            // is received, the PICC shall toggle its block number before sending a block.
            /* if (picc_target.is_for_us(addr) && !chaining &&
                !rx_driver.get_add_error    && !rx_trans_gen.get_corrupt_crc &&
                (block_num != picc_target.get_picc_block_num())) begin
                picc_target.toggle_picc_block_num;
            end */
        endtask

        virtual task send_std_r_nak(StdBlockAddress addr, logic block_num);
            super.send_std_r_nak(addr, block_num);

            handle_error_or_part4_comms_state_change;
        endtask

        virtual task send_std_s_parameters(StdBlockAddress addr, logic [7:0] inf [$]);
            super.send_std_s_parameters(addr, inf);

            handle_error_or_part4_comms_state_change;
        endtask

        virtual task send_std_s_deselect(StdBlockAddress addr);
            super.send_std_s_deselect(addr);

            handle_error_or_part4_comms_state_change;
        endtask

        // ====================================================================
        // Receiving tasks
        // ====================================================================

        // overriden so we can save a copy of the last sent message
        virtual task wait_for_reply(output reply_ready, output TxTransType reply, input logic expect_timeout=1'b0);
            super.wait_for_reply(reply_ready, reply, expect_timeout);

            if (reply_ready) begin
                // systemverilog does not support run time const objects. If anyone calls this
                // task, and then modifies the reply in anyway, this cache will also be modified.
                // So maybe we should take a deep copy?
                last_reply = reply;
            end
        endtask

        virtual task wait_for_and_verify_atqa;
            automatic TxTransType   reply;
            automatic logic         reply_ready;

            wait_for_reply(reply_ready, reply);

            if (reply_ready) begin
                void'(verify_atqa(reply));
            end
        endtask

        virtual task wait_for_and_verify_ac_reply(int sent_uid_bits);
            automatic TxTransType   reply;
            automatic logic         reply_ready;

            wait_for_reply(reply_ready, reply);

            if (reply_ready) begin
                void'(verify_ac_reply(reply, sent_uid_bits));
            end
        endtask

        virtual task wait_for_and_verify_sak(logic uid_complete);
            automatic TxTransType   reply;
            automatic logic         reply_ready;

            wait_for_reply(reply_ready, reply);

            if (reply_ready) begin
                void'(verify_sak(reply, uid_complete));
            end
        endtask

        virtual task wait_for_and_verify_ats;
            automatic TxTransType   reply;
            automatic logic         reply_ready;

            wait_for_reply(reply_ready, reply);

            if (reply_ready) begin
                void'(verify_ats(reply));
            end
        endtask

        virtual task wait_for_and_verify_ppsr;
            automatic TxTransType   reply;
            automatic logic         reply_ready;

            wait_for_reply(reply_ready, reply);

            if (reply_ready) begin
                void'(verify_ppsr(reply));
            end
        endtask

        virtual task wait_for_and_verify_std_i_block(StdBlockAddress send_addr, logic [7:0] reply_inf [$]);
            automatic TxTransType   reply;
            automatic logic         reply_ready;

            wait_for_reply(reply_ready, reply);

            if (reply_ready) begin
                void'(verify_std_i_block(reply, send_addr, reply_inf));
            end
        endtask

        virtual task wait_for_and_verify_std_r_ack(StdBlockAddress send_addr);
            automatic TxTransType   reply;
            automatic logic         reply_ready;

            wait_for_reply(reply_ready, reply);

            if (reply_ready) begin
                void'(verify_std_r_ack(reply, send_addr));
            end
        endtask

        virtual task wait_for_and_verify_resend_last;
            automatic TxTransType   reply;
            automatic TxTransType   cached_last = last_reply;
            automatic logic         reply_ready;

            wait_for_reply(reply_ready, reply);

            if (reply_ready) begin
                void'(verify_resend_last(reply, cached_last));
            end
        endtask

        virtual task wait_for_and_verify_std_s_deselect(StdBlockAddress send_addr);
            automatic TxTransType   reply;
            automatic logic         reply_ready;

            wait_for_reply(reply_ready, reply);

            if (reply_ready) begin
                void'(verify_std_s_deselect(reply, send_addr));
            end
        endtask

        // ====================================================================
        // Verifying functions
        // ====================================================================

        virtual function logic verify_atqa(TxTransType recv_trans);
            // generate the expected transaction
            automatic TxByteTransaction expected = tx_trans_gen.generate_atqa(picc_target.uid.get_size);
            return verify_trans(recv_trans, expected, EventMessageID_ATQA, "ATQA");
        endfunction

        virtual function logic verify_ac_reply(TxTransType recv_trans, int sent_uid_bits);
            // generate the expected transaction
            automatic TxByteTransaction expected = tx_trans_gen.generate_ac_reply(sent_uid_bits, picc_target.uid.get_level(picc_target.get_select_level()));
            return verify_trans(recv_trans, expected, EventMessageID_AC_REPLY, "AC_REPLY");
        endfunction

        virtual function logic verify_sak(TxTransType recv_trans, logic uid_complete);
            // generate the expected transaction
            automatic TxByteTransaction expected = tx_trans_gen.generate_sak(uid_complete);
            return verify_trans(recv_trans,
                                expected,uid_complete ? EventMessageID_SAK_COMPLETE
                                                      : EventMessageID_SAK_NOT_COMPLETE,
                                "SAK");
        endfunction

        virtual function logic verify_ats(TxTransType recv_trans);
            // generate the expected transaction
            automatic TxByteTransaction expected = tx_trans_gen.generate_ats();
            return verify_trans(recv_trans, expected, EventMessageID_ATS, "ATS");
        endfunction

        virtual function logic verify_ppsr(TxTransType recv_trans);
            // generate the expected transaction
            automatic TxByteTransaction expected = tx_trans_gen.generate_ppsr(picc_target.get_cid());
            return verify_trans(recv_trans, expected, EventMessageID_PPSR, "PPSR");
        endfunction

        virtual function logic verify_std_i_block(TxTransType recv_trans, StdBlockAddress send_addr, logic [7:0] reply_inf [$]);
            // generate the expected transaction
            automatic StdBlockAddress   reply_addr      = picc_target.get_reply_addr(send_addr);
            automatic TxByteTransaction expected        = tx_trans_gen.generate_std_i_block_for_tx(reply_addr, 1'b0, picc_target.get_picc_block_num(), reply_inf);
            automatic logic             res             = verify_trans(recv_trans, expected, EventMessageID_STD_I_BLOCK_NO_CHAINING, "STD-I (no chaining)");

            // ISO/IEC 14443-4:2016 section 7.5.4, Rule B
            // When an I-block or an R(ACK) block with a block number equal to the current block number
            // is received, the PCD shall toggle the current block number for that PICC before optionally
            // sending a block.
            if (picc_target.picc_and_pcd_block_nums_are_equal) begin
                picc_target.toggle_pcd_block_num;
            end

            return res;
        endfunction

        virtual function logic verify_std_r_ack(TxTransType recv_trans, StdBlockAddress send_addr);
            // generate the expected transaction
            automatic StdBlockAddress   reply_addr  = picc_target.get_reply_addr(send_addr);
            automatic TxByteTransaction expected    = tx_trans_gen.generate_std_r_ack_for_tx(reply_addr, picc_target.get_picc_block_num());
            automatic logic             res         = verify_trans(recv_trans, expected, EventMessageID_STD_R_ACK, "R(ACK)");

            // ISO/IEC 14443-4:2016 section 7.5.4, Rule B
            // When an I-block or an R(ACK) block with a block number equal to the current block number
            // is received, the PCD shall toggle the current block number for that PICC before optionally
            // sending a block.
            if (picc_target.picc_and_pcd_block_nums_are_equal) begin
                picc_target.toggle_pcd_block_num;
            end

            return res;
        endfunction

        virtual function logic verify_resend_last(TxTransType recv_trans, TxTransType last_received);
            automatic logic             res         = recv_trans.compare(last_received);
            automatic EventMessageID    msg_type;

            resendLastAsExpected:
            assert (res)
            else $error("Resend Last not as expected, received %s expected %s",
                        recv_trans.to_string, last_received.to_string);


            // should only occur for STD I-Block or R(ACK) blocks
            // Currently we can't decode the received transaction, as it could be in bits or bytes.
            // For now we assume it's valid, since this function should only be called after
            // we've sent a STD I-Block or an R(ACK), and the above assert confirms the reply was
            // in fact valid.
            // TODO: Re-enable this when we have message decode support

            /* if (recv_trans.data[0] ==? 8'b1010?01?) begin
                msg_type = EventMessageID_STD_R_ACK;
            end
            else if (recv_trans.data[0] ==? 8'b0000?01?) begin
                msg_type = EventMessageID_STD_I_BLOCK_NO_CHAINING;
            end
            else begin: notAckNorIBlock
                unexpectedMsgType:
                assert(0) else $error ("Resend last not R(ACK) or STD I-Block: %s", recv_trans.to_string);
                res = 1'b0;
            end
            callback_message(res ? EventCode_RECEIVED_OK : EventCode_RECEIVED_ERROR, msg_type); */

            callback_message(res ? EventCode_RECEIVED_OK : EventCode_RECEIVED_ERROR,
                             EventMessageID_UNKNOWN);

            if (res) begin

                // ISO/IEC 14443-4:2016 section 7.5.4, Rule B
                // When an I-block or an R(ACK) block with a block number equal to the current block number
                // is received, the PCD shall toggle the current block number for that PICC before optionally
                // sending a block.
                if (picc_target.picc_and_pcd_block_nums_are_equal) begin
                    picc_target.toggle_pcd_block_num;
                end
            end

            return res;
        endfunction

        virtual function logic verify_std_s_deselect(TxTransType recv_trans, StdBlockAddress send_addr);
            // generate the expected transaction
            automatic StdBlockAddress   reply_addr  = picc_target.get_reply_addr(send_addr);
            automatic TxByteTransaction expected    = tx_trans_gen.generate_std_s_deselect_for_tx(reply_addr);
            automatic logic             res         = verify_trans(recv_trans, expected, EventMessageID_STD_S_DESELECT, "S(DESELECT)");

            // we don't check that the addr mateches the PICC's because this is the reply from the PICC
            // either it's a valid S(DESELECT) reply, in which case great. Or it's some other msg
            // and the above assertion will have failed

            // once the reply has been sent the state change to State_HALT occurs
            // again we don't need to check the current state here, as since the PICC responded
            // it must transition to State_HALT
            register_state_change(State_HALT);

            return res;
        endfunction

        // ====================================================================
        // send message verify reply tasks
        // ====================================================================

        virtual task send_reqa_verify_reply;
            send_reqa;
            wait_for_and_verify_atqa;
        endtask

        virtual task send_wupa_verify_reply;
            send_wupa;
            wait_for_and_verify_atqa;
        endtask

        virtual task send_ac_verify_reply(int uid_bits);
            automatic int curr_level = picc_target.get_select_level();
            send_ac_select(curr_level, uid_bits, picc_target.uid.get_level(curr_level));
            wait_for_and_verify_ac_reply(uid_bits);
        endtask

        virtual task send_select_verify_reply;
            automatic int curr_level = picc_target.get_select_level();
            send_select(curr_level, picc_target.uid.get_level(curr_level));
            wait_for_and_verify_sak(picc_target.uid.get_num_levels() == (curr_level + 1));
        endtask

        virtual task send_rats_verify_reply(logic [3:0] fsdi, logic [3:0] cid);
            send_rats(fsdi, cid);
            wait_for_and_verify_ats;
        endtask

        virtual task send_pps_verify_reply(logic p1_present, logic [1:0] dsi, logic [1:0] dri);
            send_pps(picc_target.get_cid(), p1_present, dsi, dri);
            wait_for_and_verify_ppsr;
        endtask

        virtual task send_std_i_block_verify_reply(StdBlockAddress addr, logic [7:0] send_inf [$], logic [7:0] reply_inf [$]);
            send_std_i_block(addr, 1'b0, picc_target.get_pcd_block_num(), send_inf);
            wait_for_and_verify_std_i_block(addr, reply_inf);
        endtask

        // Should only be called when the PCD's and PICC's block numbers are not equal
        virtual task send_std_r_nak_correct_block_num_verify_reply(StdBlockAddress addr);
            send_std_r_nak(addr, picc_target.get_pcd_block_num);
            wait_for_and_verify_std_r_ack(addr);
        endtask

        // Should only be called when the PCD's and PICC's block numbers are equal
        virtual task send_std_r_ack_verify_resend_last(StdBlockAddress addr);
            send_std_r_ack(addr, picc_target.get_pcd_block_num());
            wait_for_and_verify_resend_last;
        endtask

        // Should only be called when the PCD's and PICC's block numbers are equal
        virtual task send_std_r_nak_verify_resend_last(StdBlockAddress addr);
            send_std_r_nak(addr, picc_target.get_pcd_block_num());
            wait_for_and_verify_resend_last;
        endtask

        virtual task send_std_s_deselect_verify_reply(StdBlockAddress addr);
            send_std_s_deselect(addr);
            wait_for_and_verify_std_s_deselect(addr);
        endtask

        // ====================================================================
        // State transition functions / tasks
        // ====================================================================

        virtual protected function void register_no_state_change;
            if (!disable_state_tracking) begin
                specific_target_callback_state(SpecificTargetEventCode_REMAINING_IN_STATE, picc_state);
            end
        endfunction

        virtual function void register_state_change(State new_state);
            if (!disable_state_tracking) begin
                if (picc_state != new_state) begin
                    picc_state = new_state;
                    specific_target_callback_state(SpecificTargetEventCode_ENTERED_STATE, new_state);
                end
            end
        endfunction

        virtual function void handle_error_or_part4_comms_state_change;
            // Any error / invalid message returns to idle / halt when in the initialisation stage
            // any part4 comms message (other than RATS) is treated as an error in the
            // initialisation stage.
            // Any message received in the PPS_ALLOWED state, moves us to the STD_COMMS state.

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
        endfunction

        virtual function logic is_in_star_state;
            case (picc_state)
                State_IDLE:                 return 1'b0;
                State_READY:                return 1'b0;
                State_ACTIVE:               return 1'b0;
                State_HALT:                 return 1'b1;
                State_READY_STAR:           return 1'b1;
                State_ACTIVE_STAR:          return 1'b1;
                State_PROTOCOL_PPS_ALLOWED: return 1'b0;
                State_PROTOCOL_STD_COMMS:   return 1'b0;
                default:                    $fatal(0, "state: %s not supported", picc_state.name);
            endcase
        endfunction

        virtual protected task select_tag;
            // assume we are in state Ready / Ready_STAR at select level 0

            repeat(picc_target.uid.get_num_levels()) begin
                send_select_verify_reply;
            end
        endtask

        virtual task go_to_state_idle;
            if (picc_state == State_IDLE) begin
                // already there
                return;
            end

            // it is impossible to reach State_IDLE from any of the star states
            // and it's quicker to reach idle via a reset than sending a message
            // that will return us there.
            do_reset;
            register_state_change(State_IDLE);
        endtask

        virtual task go_to_state_ready;
            if ((picc_state == State_READY) &&
                (picc_target.get_select_level() == 0)) begin
                // already there
                return;
            end

            go_to_state_idle;

            // we can get to ready by sending REQA or WUPA
            if (1'($urandom)) begin
                send_reqa_verify_reply;
            end
            else begin
                send_wupa_verify_reply;
            end
        endtask

        virtual task go_to_state_active;
            if (picc_state == State_ACTIVE) begin
                // already there
                return;
            end

            go_to_state_ready;
            select_tag;
        endtask

        virtual task go_to_state_halt;
            if (picc_state == State_HALT) begin
                // already there
            end
            else if ((picc_state == State_IDLE) || (picc_state == State_READY)) begin
                // we have to go to State_ACTIVE then send a HLTA
                go_to_state_active;
                send_hlta_verify_no_reply;
            end
            else if (is_in_star_state() || (picc_state == State_ACTIVE)) begin
                // just send a HLTA
                send_hlta_verify_no_reply;
            end
            else begin
                // in the protocol state, send S(DESELECT)
                send_std_s_deselect_verify_reply(picc_target.get_addr());
            end
        endtask

        virtual task go_to_state_ready_star;
            if ((picc_state == State_READY_STAR) &&
                (picc_target.get_select_level() == 0)) begin
                // already there
                return;
            end

            go_to_state_halt;

            // Can't use REQA here, has to be WUPa
            send_wupa_verify_reply;
        endtask

        virtual task go_to_state_active_star;
            if (picc_state == State_ACTIVE_STAR) begin
                // already there
                return;
            end

            go_to_state_ready_star;
            select_tag;
        endtask

        virtual task go_to_state_expect_rats;
            // We expect RATS in State_ACTIVE and State_ACTIVE_STAR
            // go to whichever is closer
            if (is_in_star_state) begin
                // from State_HALT or State_READY_STAR, it's quicker to get to State_ACTIVE_STAR
                go_to_state_active_star;
            end
            else begin
                // from State_IDLE or State_READY, it's quicker to get to State_ACTIVE
                // From State_PROTOCOL_STD_COMMS it's quicker to reset to idle than to send S(DESELECT)
                go_to_state_active;
            end
        endtask

        virtual task go_to_state_protocol_pps_allowed(CidType cid_type = CID_CURRENT);
            if ((picc_state == State_PROTOCOL_PPS_ALLOWED) &&
                (cid_type == CID_CURRENT)) begin
                // already there
                return;
            end

            go_to_state_expect_rats;

            // send RATS with a random FSDI
            send_rats_verify_reply(4'($urandom), get_cid_from_cid_type(cid_type));
        endtask

        // if cid is -1 (default) we use a random (valid) CID
        virtual task go_to_state_protocol_std_comms(CidType cid_type = CID_CURRENT);
            if ((picc_state == State_PROTOCOL_STD_COMMS) &&
                (cid_type == CID_CURRENT)) begin
                // already there
                return;
            end

            go_to_state_protocol_pps_allowed(cid_type);

            // we can send any message at all at this point but we may as well send the PPS
            // We send DSI and DRI == 0 here, as the DUT does not support others
            // we randomly add the P1 field
            send_pps_verify_reply(1'($urandom), 0, 0);
        endtask

        // if cid is -1 (default) we use a random (valid) CID
        virtual task go_to_state (State state, CidType cid_type = CID_CURRENT);
            case (state)
                State_IDLE:                 go_to_state_idle;
                State_READY:                go_to_state_ready;
                State_ACTIVE:               go_to_state_active;
                State_HALT:                 go_to_state_halt;
                State_READY_STAR:           go_to_state_ready_star;
                State_ACTIVE_STAR:          go_to_state_active_star;
                State_PROTOCOL_PPS_ALLOWED: go_to_state_protocol_pps_allowed(cid_type);
                State_PROTOCOL_STD_COMMS:   go_to_state_protocol_std_comms(cid_type);
                default:                    $fatal(0, "state: %s not supported", state.name);
            endcase
        endtask
    endclass


endpackage
