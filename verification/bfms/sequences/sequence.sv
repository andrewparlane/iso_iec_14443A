/***********************************************************************
        File: sequence.sv
 Description: Base class for sending and receiving messages
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

package sequence_pkg;

    import std_block_address_pkg::StdBlockAddress;

    // This base class is designed so that we can send any PCD -> PICC message
    // and verify the reply. It is not designed to test the intricacies of every module.
    // It can and should be extended to do these things.
    // Examples:
    //  Act as a PCD discovering what PICCs are there and communicate with each.
    //  Test that the initialisation module responds to every message correctly in every state.
    //  Test that the iso14443_4a module responds correctly to each message in every state.

    class Sequence
    #(
        // These must extend QueueTransaction
        type RxTransType,
        type TxTransType,

        // This must extend RxDriver
        type RxDriverType,

        // This must extend TxMonitor
        type TxMonitorType
    );

        typedef logic [7:0] ByteQueue [$];

        // event codes for use with the callback function
        typedef enum
        {
            // These use EventMessageID as the arg
            EventCode_SENDING,
            EventCode_SENT,
            EventCode_RECEIVED_OK,
            EventCode_RECEIVED_ERROR
        } EventCode;

        typedef enum
        {
            // PCD -> PICC
            EventMessageID_REQA,
            EventMessageID_WUPA,
            EventMessageID_HLTA,
            EventMessageID_AC,
            EventMessageID_SELECT,
            EventMessageID_RATS,
            EventMessageID_PPS,

            // PICC -> PCD
            EventMessageID_ATQA,
            EventMessageID_AC_REPLY,
            EventMessageID_SAK_NOT_COMPLETE,
            EventMessageID_SAK_COMPLETE,
            EventMessageID_ATS,
            EventMessageID_PPSR,                // note that the actual message is just PPS, PPSR is my own terminology

            // STD blocks (bidirectional)
            EventMessageID_STD_I_BLOCK_CHAINING,
            EventMessageID_STD_I_BLOCK_NO_CHAINING,
            EventMessageID_STD_R_ACK,
            EventMessageID_STD_R_NAK,
            EventMessageID_STD_S_DESELECT,
            EventMessageID_STD_S_PARAMETERS,

            // misc (bidirectional)
            EventMessageID_RANDOM_NON_VALID,    // not used here, but our child classes need it
            EventMessageID_UNKNOWN
        } EventMessageID;

        // Our transaction generators
        typedef rx_transaction_generator_pkg::RxTransactionGenerator
        #(
            .TransType(RxTransType)
        ) RxTransGenType;

        typedef tx_transaction_generator_pkg::TxTransactionGenerator
        #(
            .TransType(TxTransType)
        ) TxTransGenType;

        RxTransGenType rx_trans_gen;
        TxTransGenType tx_trans_gen;

        // The send_queue and recv_queue
        // They are wrapped in classes so that we can store a reference to them
        // rather than a copy
        typedef RxTransType                                     RxTransQueueType [$];
        typedef TxTransType                                     TxTransQueueType [$];
        typedef wrapper_pkg::Wrapper #(.Type(RxTransQueueType)) RxQueueWrapperType;
        typedef wrapper_pkg::Wrapper #(.Type(TxTransQueueType)) TxQueueWrapperType;

        RxQueueWrapperType rx_send_queue;
        TxQueueWrapperType tx_recv_queue;

        // The driver / monitor (these are references)
        RxDriverType    rx_driver;
        TxMonitorType   tx_monitor;

        // Timing
        int             reply_timeout;

        // constructor
        function new(RxTransGenType             _rx_trans_gen,
                     TxTransGenType             _tx_trans_gen,
                     RxQueueWrapperType         _rx_send_queue,
                     TxQueueWrapperType         _tx_recv_queue,
                     RxDriverType               _rx_driver,
                     TxMonitorType              _tx_monitor,
                     int                        _reply_timeout);
            rx_trans_gen    = _rx_trans_gen;
            tx_trans_gen    = _tx_trans_gen;
            rx_send_queue   = _rx_send_queue;
            tx_recv_queue   = _tx_recv_queue;
            rx_driver       = _rx_driver;
            tx_monitor      = _tx_monitor;
            reply_timeout   = _reply_timeout;
        endfunction

        // ====================================================================
        // Callbacks
        // ====================================================================

        // since SV doesn't have function pointers I expect the testbench to extend this class
        // or one of it's child classes and override callback. It can interpret the events as
        // it wishes.
        // We use int for the arg rather than specific enums,
        // so that child classes may provide additional information
        virtual protected function void sequence_callback(EventCode ec, int arg=0);
        endfunction

        // this is just a wrapper around callback, for EventCodes that use EventMessageID
        // as the argument
        virtual protected function void callback_message(EventCode ec, EventMessageID mid);
            sequence_callback(ec, int'(mid));
        endfunction

        // ====================================================================
        // Sending tasks
        // ====================================================================

        virtual task send_transaction (RxTransType trans, EventMessageID mid);
            // push it to the send queue
            rx_send_queue.data.push_back(trans);
            callback_message(EventCode_SENDING, mid);

            // wait for it to have been sent
            rx_driver.wait_for_idle(rx_driver.calculate_send_time(trans) + 100);
            callback_message(EventCode_SENT, mid);
        endtask

        virtual task send_reqa;
            send_transaction(rx_trans_gen.generate_reqa(), EventMessageID_REQA);
        endtask

        virtual task send_wupa;
            send_transaction(rx_trans_gen.generate_wupa(), EventMessageID_WUPA);
        endtask

        virtual task send_hlta;
            send_transaction(rx_trans_gen.generate_hlta(), EventMessageID_HLTA);
        endtask

        virtual task send_ac_select(int level, int uid_bits, logic [31:0] uid, logic toggle_last_bcc_bit=1'b0);
            /* $display("send_ac_select level %d, uid_bits %d, uid %x, toggle_last_bcc_bit %b",
                     level, uid_bits, uid, toggle_last_bcc_bit); */
            send_transaction(rx_trans_gen.generate_ac_select(level, uid_bits, uid, toggle_last_bcc_bit),
                             (uid_bits == 32) ? EventMessageID_SELECT
                                              : EventMessageID_AC);
        endtask

        virtual task send_ac(int level, int uid_bits, logic [31:0] uid);
            uidBitsNot32: assert(uid_bits != 32) else $error("send_ac() called with uid_bits == 32");
            send_ac_select(level, uid_bits, uid);
        endtask

        virtual task send_select(int level, logic [31:0] uid, logic toggle_last_bcc_bit=1'b0);
            //$display("sending SELECT level %d, uid %x", level, uid);
            send_ac_select(level, 32, uid, toggle_last_bcc_bit);
        endtask

        virtual task send_rats(logic [3:0] fsdi, logic [3:0] cid);
            send_transaction(rx_trans_gen.generate_rats(fsdi, cid), EventMessageID_RATS);
        endtask

        virtual task send_pps(logic [3:0] cid, logic p1_present, logic [1:0] dsi, logic [1:0] dri);
            send_transaction(rx_trans_gen.generate_pps(cid, p1_present, dsi, dri), EventMessageID_PPS);
        endtask

        virtual task send_std_i_block(StdBlockAddress addr, logic chaining, logic block_num, logic [7:0] inf [$]);
            send_transaction(rx_trans_gen.generate_std_i_block(addr, chaining, block_num, inf),
                             chaining ? EventMessageID_STD_I_BLOCK_CHAINING
                                      : EventMessageID_STD_I_BLOCK_NO_CHAINING);
        endtask

        virtual task send_std_r_ack(StdBlockAddress addr, logic block_num);
            send_transaction(rx_trans_gen.generate_std_r_ack(addr, block_num),
                             EventMessageID_STD_R_ACK);
        endtask

        virtual task send_std_r_nak(StdBlockAddress addr, logic block_num);
            send_transaction(rx_trans_gen.generate_std_r_nak(addr, block_num),
                             EventMessageID_STD_R_NAK);
        endtask

        virtual task send_std_s_deselect(StdBlockAddress addr);
            send_transaction(rx_trans_gen.generate_std_s_deselect(addr),
                             EventMessageID_STD_S_DESELECT);
        endtask

        virtual task send_std_s_parameters(StdBlockAddress addr, logic [7:0] inf [$]);
            send_transaction(rx_trans_gen.generate_std_s_parameters(addr, inf),
                             EventMessageID_STD_S_PARAMETERS);
        endtask

        // ====================================================================
        // Receiving tasks
        // ====================================================================
        // note: we only have generic functions / tasks here as this class should be used
        //       as the base class for all ISO/IEC 14443A comms tests. There could be no target
        //       present, or the target could be in the wrong state for a message, etc..

        virtual task wait_for_reply(output reply_ready, output TxTransType reply, input logic expect_timeout=1'b0);
            tx_monitor.wait_for_packet_received(reply_timeout, !expect_timeout);

            replyReceived:
                assert (tx_recv_queue.data.size() == (expect_timeout ? 0 : 1))
                else $error("%d replies in the tx_recv_queue, expected %d",
                             tx_recv_queue.data.size,
                             (expect_timeout ? 0 : 1));

            reply_ready = 1'b0;
            if (tx_recv_queue.data.size()) begin
                reply_ready = 1'b1;
                reply       = tx_recv_queue.data.pop_front;
            end
        endtask

        virtual task verify_no_reply;
            automatic TxTransType   reply;
            automatic logic         reply_ready;

            wait_for_reply(reply_ready, reply, 1'b1);

            noReply: assert(!reply_ready) else $error("Expecting no reply, but got %s", reply.to_string);
        endtask

        virtual task wait_for_and_verify_trans(TxTransType expected, int msgType);
            automatic TxTransType   reply;
            automatic logic         reply_ready;

            wait_for_reply(reply_ready, reply);

            if (reply_ready) begin
                void'(verify_trans(reply, expected, msgType));
            end
        endtask

        // ====================================================================
        // Verifying functions
        // ====================================================================
        // note: we only have generic functions / tasks here as this class should be used
        //       as the base class for all ISO/IEC 14443A comms tests. There could be no target
        //       present, or the target could be in the wrong state for a message, etc..

        virtual function logic verify_trans(TxTransType recv_trans, TxTransType expected, int msgType);
            // generate the expected transaction
            automatic logic res = recv_trans.compare(expected);

            transAsExpected:
            assert (res)
            else $error("Transaction not as expected, received %s expected %s",
                        recv_trans.to_string, expected.to_string);

            sequence_callback(res ? EventCode_RECEIVED_OK : EventCode_RECEIVED_ERROR,
                              msgType);

            return res;
        endfunction

        // ====================================================================
        // send message verify reply tasks
        // ====================================================================
        // note: we only have generic functions / tasks here as this class should be used
        //       as the base class for all ISO/IEC 14443A comms tests. There could be no target
        //       present, or the target could be in the wrong state for a message, etc..

        virtual task send_hlta_verify_no_reply;
            send_hlta;
            verify_no_reply;
        endtask

    endclass


endpackage
