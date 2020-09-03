/***********************************************************************
        File: transaction_generator.sv
 Description: Base class for generation of Rx / Tx transactions
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

package transaction_generator_pkg;

    import std_block_address_pkg::StdBlockAddress;

    import queue_transaction_pkg::*;

    import rx_byte_transaction_pkg::*;
    import tx_byte_transaction_pkg::*;

    class TransactionGenerator;

        protected logic auto_append_crc;
        protected logic corrupt_crc;

        function new (logic _auto_append_crc);
            auto_append_crc = _auto_append_crc;
            corrupt_crc     = 1'b0;
        endfunction

        virtual function void set_auto_append_crc(logic _auto_append_crc);
            auto_append_crc = _auto_append_crc;
        endfunction

        virtual function void set_corrupt_crc(logic _corrupt_crc);
            corrupt_crc = _corrupt_crc;
        endfunction

        virtual function logic get_corrupt_crc;
            return corrupt_crc;
        endfunction

        virtual function void append_crc(ByteQueueTransaction trans);
            if (auto_append_crc) begin
                trans.append_crc;
                if (corrupt_crc) begin
                    automatic int corrupt_crc_byte  = $urandom_range(1);
                    automatic int corrupt_crc_bit   = $urandom_range(7);

                    trans.data[$-corrupt_crc_byte][corrupt_crc_bit] = !trans.data[$-corrupt_crc_byte][corrupt_crc_bit];
                end
            end
        endfunction

        // ====================================================================
        // IOS/IEC 14443-3A messages for Rx
        // ====================================================================

        // Messages
        //  REQA
        //  WUPA
        //  HLTA
        //  SELECT/AC

        function RxByteTransaction generate_reqa;
            automatic RxByteTransaction trans = new('{{1'($urandom), ISO14443A_pkg::REQA}}, 7);
            // this doesn't have a CRC because it's only 7 bits
            return trans;
        endfunction

        function RxByteTransaction generate_wupa;
            automatic RxByteTransaction trans = new('{{1'($urandom), ISO14443A_pkg::WUPA}}, 7);
            // this doesn't have a CRC because it's only 7 bits
            return trans;
        endfunction

        function RxByteTransaction generate_hlta;
            automatic RxByteTransaction trans = new('{ISO14443A_pkg::HLTA[7:0], ISO14443A_pkg::HLTA[15:8]});
            // add the CRC if we are auto-adding them
            append_crc(trans);
            return trans;
        endfunction

        // ANTI COLLISION / SELECT
        function RxByteTransaction generate_ac_select(int level, int uid_bits, logic [31:0] uid, logic toggle_last_bcc_bit = 1'b0);
            automatic RxByteTransaction trans = new;

            // the AC/SELECT message is: sel, nvb, uid0, uid1, uid2, uid3, bcc
            automatic int           whole_bytes_to_send = 2 + (uid_bits / 8);
            automatic logic [7:0]   bcc                 = uid[31:24] ^ uid[23:16] ^ uid[15:8] ^ uid[7:0];

            if (toggle_last_bcc_bit) begin
                // for testing purposes to make sure we match the entire UID including the BCC
                bcc[7] = !bcc[7];
            end

            if (uid_bits == 32) begin
                // send all of the UID so add BCC
                whole_bytes_to_send++;
            end

            trans.bits_in_last_byte = uid_bits % 8;

            // SEL
            case (level)
                0: trans.push_back(ISO14443A_pkg::SEL1);
                1: trans.push_back(ISO14443A_pkg::SEL2);
                2: trans.push_back(ISO14443A_pkg::SEL3);
                default: $fatal(0, "Invalid level %d passed to generate_ac_select", level);
            endcase

            // NVB
            trans.push_back({4'(whole_bytes_to_send), 4'(trans.bits_in_last_byte)});

            // UID
            for (int i = uid_bits; i > 0; i-=8) begin
                trans.push_back(uid[7:0]);
                uid = {8'h0, uid[31:8]};
            end
            // randomise any "not sent" bits
            if ((uid_bits % 8) != 0) begin
                for (int i = 7; i >= (uid_bits % 8); i--) begin
                    trans.data[$][i] = 1'($urandom);
                end
            end

            // if it's a SELECT
            if (uid_bits == 32) begin
                // BCC
                trans.push_back(bcc);

                // add the CRC if we are auto-adding them
                append_crc(trans);
            end

            return trans;
        endfunction

        // ====================================================================
        // IOS/IEC 14443-3A messages for Tx
        // ====================================================================

        // Messages are:
        //  ATQA                - response to REQA / WUPA
        //  AC reply            - response to AC
        //  SAK                 - response to SELECT

        function TxByteTransaction generate_atqa(ISO14443A_pkg::UIDSize uid_size);
            automatic logic [15:0]  ATQA_REPLY  = ISO14443A_pkg::ATQA(uid_size);
            automatic TxByteTransaction trans   = new('{ATQA_REPLY[7:0], ATQA_REPLY[15:8]});
            // this doesn't have a CRC
            return trans;
        endfunction

        function TxByteTransaction generate_ac_reply(int uid_bits_sent, logic [31:0] uid);
            automatic TxByteTransaction trans   = new;
            automatic logic [7:0]       bcc     = uid[31:24] ^ uid[23:16] ^ uid[15:8] ^ uid[7:0];

            // the AC/SELECT message is: sel, nvb, uid0, uid1, uid2, uid3, bcc
            // sel and nvb have to be sent by the PCD. Then any number of UID bits
            // can be sent. If all 32 UID bits are sent, the BCC must also be sent.
            // and then it becomes a SELECT rather than an AC, which we don't deal with here.
            // The PICC replies to an AC message with all the remaining UID bits and the BCC.
            automatic int whole_uid_bytes_sent  = uid_bits_sent / 8;

            if ((uid_bits_sent % 8) == 0) begin
                // the request ended with a full byte
                // so the reply starts with one
                trans.bits_in_first_byte = 0;
            end
            else begin
                // the request ended with a partial byte
                // so the reply starts with the remaining bits
                trans.bits_in_first_byte = 8 - (uid_bits_sent % 8);
            end

            // shift out full bytes
            repeat (whole_uid_bytes_sent) begin
                uid = {8'h00, uid[31:8]};
            end

            // add the remaining bytes to the data queue
            repeat (4 - whole_uid_bytes_sent) begin
                trans.push_back(uid[7:0]);
                uid = {8'h00, uid[31:8]};
            end

            // and the BCC
            trans.push_back(bcc);

            // finally adjust the first byte, to remove the bits already sent
            if (uid_bits_sent != 32) begin   // all bits sent, nothing to shift
                repeat (uid_bits_sent % 8) begin
                    trans.data[0] = {1'($urandom), trans.data[0][7:1]};
                end
            end

            // this doesn't have a CRC
            return trans;
        endfunction

        function TxByteTransaction generate_sak(logic uid_complete);
            automatic TxByteTransaction trans = new;

            trans.push_back(uid_complete ? ISO14443A_pkg::SAK_UID_COMPLETE
                                         : ISO14443A_pkg::SAK_UID_NOT_COMPLETE);

            // add the CRC if we are auto-adding them
            append_crc(trans);
            return trans;
        endfunction

        // ====================================================================
        // IOS/IEC 14443-4 std blocks, for Rx or Tx
        // ====================================================================

        // Messages
        //  I-Block
        //      with / without chaining
        //  R-Block
        //      R(ACK)
        //      R(NAK)
        //  S-Block
        //      S(DESELECT)
        //      S(PARAMETERS)
        //      S(WTX)          - not supported

        protected function ByteQueueTransaction generate_std_block (StdBlockAddress addr, logic [7:0] pcb, logic is_rx, logic [7:0] inf [$] = '{});
            automatic ByteQueueTransaction trans = new;

            // PCB
            // we overwrite the has_cid and has_nad fields based on addr
            // NOTE: NAD is only allowed for STD I-Blocks. We do not verify this here.
            pcb[3] = addr.has_cid;
            pcb[2] = addr.has_nad;
            trans.push_back(pcb);

            // CID
            if (addr.has_cid) begin
                // ISO/IEC 14443-4:2016 section 7.1.2.2
                // The two most significant bits b8 and b7 are used to indicate the
                // power level indication received by a PICC from a PCD.
                // These two bits shall be set to (00)b for PCD to PICC communication.
                automatic logic [1:0] power = is_rx ? 2'b00 : addr.power;

                trans.push_back({power, 2'b00, addr.cid});
            end
            // NAD
            if (addr.has_nad) begin
                trans.push_back(addr.nad);
            end
            // INF
            trans.push_back_queue(inf);

            // add the CRC if we are auto-adding them
            append_crc(trans);
            return trans;
        endfunction

        function ByteQueueTransaction generate_std_i_block (StdBlockAddress addr, logic is_rx, logic chaining, logic block_num, logic [7:0] inf [$]);
            automatic logic [7:0] pcb = {3'b000, chaining, 3'b001, block_num};
            return generate_std_block(addr, pcb, is_rx, inf);
        endfunction

        function ByteQueueTransaction generate_std_r_block (StdBlockAddress addr, logic is_rx, logic nak, logic block_num);
            automatic logic [7:0] pcb = {3'b101, nak, 3'b001, block_num};
            return generate_std_block(addr, pcb, is_rx);
        endfunction

        function ByteQueueTransaction generate_std_r_ack(StdBlockAddress addr, logic is_rx, logic block_num);
            return generate_std_r_block(addr, is_rx, 1'b0, block_num);
        endfunction

        function ByteQueueTransaction generate_std_r_nak(StdBlockAddress addr, logic is_rx, logic block_num);
            return generate_std_r_block(addr, is_rx, 1'b1, block_num);
        endfunction

        function ByteQueueTransaction generate_std_s_block (StdBlockAddress addr, logic is_rx, logic [1:0] b6_5, logic b2, logic [7:0] inf [$] = '{});
            automatic logic [7:0] pcb = {2'b11, b6_5, 2'b00, b2, 1'b0};
            return generate_std_block(addr, pcb, is_rx, inf);
        endfunction

        function ByteQueueTransaction generate_std_s_deselect(StdBlockAddress addr, logic is_rx);
            return generate_std_s_block(addr, is_rx, 2'b00, 1'b1);
        endfunction

        function ByteQueueTransaction generate_std_s_parameters(StdBlockAddress addr, logic is_rx, logic [7:0] inf [$]);
            return generate_std_s_block(addr, is_rx, 2'b11, 1'b0, inf);
        endfunction

        // ====================================================================
        // IOS/IEC 14443-4 std blocks, for Rx
        // ====================================================================

        function RxByteTransaction generate_std_i_block_for_rx (StdBlockAddress addr, logic chaining, logic block_num, logic [7:0] inf [$]);
            automatic ByteQueueTransaction  bt  = generate_std_i_block(addr, 1'b1, chaining, block_num, inf);
            automatic RxByteTransaction     res = new(bt.data);
            return res;
        endfunction

        function RxByteTransaction generate_std_r_ack_for_rx(StdBlockAddress addr, logic block_num);
            automatic ByteQueueTransaction  bt  = generate_std_r_ack(addr, 1'b1, block_num);
            automatic RxByteTransaction     res = new(bt.data);
            return res;
        endfunction

        function RxByteTransaction generate_std_r_nak_for_rx(StdBlockAddress addr,logic block_num);
            automatic ByteQueueTransaction  bt  = generate_std_r_nak(addr, 1'b1, block_num);
            automatic RxByteTransaction     res = new(bt.data);
            return res;
        endfunction

        function RxByteTransaction generate_std_s_deselect_for_rx(StdBlockAddress addr);
            automatic ByteQueueTransaction  bt  = generate_std_s_deselect(addr, 1'b1);
            automatic RxByteTransaction     res = new(bt.data);
            return res;
        endfunction

        function RxByteTransaction generate_std_s_parameters_for_rx(StdBlockAddress addr, logic [7:0] inf [$]);
            automatic ByteQueueTransaction  bt  = generate_std_s_parameters(addr, 1'b1, inf);
            automatic RxByteTransaction     res = new(bt.data);
            return res;
        endfunction

        // ====================================================================
        // IOS/IEC 14443-4 std blocks, for Tx
        // ====================================================================

        function TxByteTransaction generate_std_i_block_for_tx (StdBlockAddress addr, logic chaining, logic block_num, logic [7:0] inf [$]);
            automatic ByteQueueTransaction  bt  = generate_std_i_block(addr, 1'b0, chaining, block_num, inf);
            automatic TxByteTransaction     res = new(bt.data);
            return res;
        endfunction

        function TxByteTransaction generate_std_r_ack_for_tx(StdBlockAddress addr, logic block_num);
            automatic ByteQueueTransaction  bt  = generate_std_r_ack(addr, 1'b0, block_num);
            automatic TxByteTransaction     res = new(bt.data);
            return res;
        endfunction

        function TxByteTransaction generate_std_r_nak_for_tx(StdBlockAddress addr,logic block_num);
            automatic ByteQueueTransaction  bt  = generate_std_r_nak(addr, 1'b0, block_num);
            automatic TxByteTransaction     res = new(bt.data);
            return res;
        endfunction

        function TxByteTransaction generate_std_s_deselect_for_tx(StdBlockAddress addr);
            automatic ByteQueueTransaction  bt  = generate_std_s_deselect(addr, 1'b0);
            automatic TxByteTransaction     res = new(bt.data);
            return res;
        endfunction

        function TxByteTransaction generate_std_s_parameters_for_tx(StdBlockAddress addr, logic [7:0] inf [$]);
            automatic ByteQueueTransaction  bt  = generate_std_s_parameters(addr, 1'b0, inf);
            automatic TxByteTransaction     res = new(bt.data);
            return res;
        endfunction

        // ====================================================================
        // IOS/IEC 14443-4A messages (not STD Blocks) for Rx
        // ====================================================================

        // Messages
        //  RATS
        //  PPS

        function RxByteTransaction generate_rats (logic [3:0] fsdi, logic [3:0] cid);
            automatic RxByteTransaction trans = new;

            trans.push_back(ISO14443A_pkg::RATS);
            trans.push_back({fsdi, cid});

            // add the CRC if we are auto-adding them
            append_crc(trans);
            return trans;
        endfunction

        function RxByteTransaction generate_pps (logic [3:0] cid, logic p1_present, logic [1:0] dsi, logic [1:0] dri);
            automatic RxByteTransaction trans = new;

            trans.push_back({ISO14443A_pkg::PPSS, cid});       // PPSS
            trans.push_back({3'b000, p1_present, 4'b0001});    // PPS0
            if (p1_present) begin
                trans.push_back({4'b0000, dsi, dri});          // PPS1
            end

            // add the CRC if we are auto-adding them
            append_crc(trans);
            return trans;
        endfunction

        // ====================================================================
        // IOS/IEC 14443-4A messages (not STD Blocks) for Rx
        // ====================================================================

        // Messages
        //  ATS                 - response to RATS
        //  PPSR                - response to PPS

        function TxByteTransaction generate_ats;
            // our ATS reply is just the TL field, which is the length including itself (= 1)
            automatic TxByteTransaction trans = new('{8'd1});

            // add the CRC if we are auto-adding them
            append_crc(trans);
            return trans;
        endfunction

        function TxByteTransaction generate_ppsr (logic [3:0] cid);
            automatic TxByteTransaction trans = new;

            // The response to PPS is just the PPSS byte including the CID
            trans.data.push_back({ISO14443A_pkg::PPSS, cid});

            // add the CRC if we are auto-adding them
            append_crc(trans);
            return trans;
        endfunction

        // ====================================================================
        // Misc for Rx
        // ====================================================================

        function RxByteTransaction generate_from_byte_queue_for_rx(logic [7:0] bq [$], int bits_in_last_byte=0);
            automatic RxByteTransaction trans = new(bq, bits_in_last_byte);
            if (bits_in_last_byte == 0) begin
                // add the CRC if we are auto-adding them
                append_crc(trans);
            end
            return trans;
        endfunction

        // random transaction that should not be accepted as any valid 14443-3A or 14443-4A Rx frames.
        function RxByteTransaction generate_random_non_valid(int num_bytes);
            automatic logic [7:0] bq [$] = '{};

            // We don't want this to be any valid ISO/IEC 14443-3A / -4A message.
            for (int i = 0; i < num_bytes; i++) begin
                automatic logic [7:0] b;

                // don't let first byte be REQA, WUPA, HLTA[0], SELn, RATS, PPS, STD-[ISR]
                if (i == 0) begin
                    std::randomize(b) with
                    {
                        b[6:0]                  != ISO14443A_pkg::REQA;
                        b[6:0]                  != ISO14443A_pkg::WUPA;
                        b                       != ISO14443A_pkg::HLTA[7:0];
                        b                       != ISO14443A_pkg::SEL1;
                        b                       != ISO14443A_pkg::SEL2;
                        b                       != ISO14443A_pkg::SEL3;
                        b                       != ISO14443A_pkg::RATS;
                        b[7:4]                  != ISO14443A_pkg::PPSS;
                        {b[7:5], b[1]}          != 4'b0001;                 // STD-I
                        {b[7:5], b[2:1]}        != 5'b10101;                // STD-R
                        {b[7:6], b[2], b[0]}    != 4'b1100;                 // STD-S
                    };
                end
                else begin
                    std::randomize(b);
                end

                bq.push_back(b);
            end

            return generate_from_byte_queue_for_rx(bq, 0);
        endfunction

        // ====================================================================
        // Misc for Tx
        // ====================================================================

        function TxByteTransaction generate_from_byte_queue_for_tx(logic [7:0] bq [$], int bits_in_first_byte=0);
            automatic TxByteTransaction trans = new(bq, bits_in_first_byte);
            if (bits_in_first_byte == 0) begin
                // add the CRC if we are auto-adding them
                append_crc(trans);
            end
            return trans;
        endfunction

    endclass

endpackage
