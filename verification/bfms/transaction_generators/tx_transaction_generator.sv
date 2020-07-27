/***********************************************************************
        File: tx_transaction_generator.sv
 Description: Base class for generation of Tx transactions
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

package tx_transaction_generator_pkg;

    virtual class TxTransactionGenerator
    #(
        type TransType  // must extend QueueTransaction
    )
    extends transaction_generator_pkg::TransactionGenerator
    #(
        .TransType      (TransType),
        .ByteTransType  (tx_byte_transaction_pkg::TxByteTransaction)
    );

        // We generate everything as TxByteTransaction by default, child classes then convert
        // this to their own transaction format

        function new (logic _auto_append_crc);
            super.new(_auto_append_crc);
        endfunction

        virtual protected function logic is_rx_trans_gen;
            return 1'b0;
        endfunction

        // PICC -> PCD messages are:
        //  ATQA                - response to REQA / WUPA
        //  AC reply            - response to AC
        //  SAK                 - response to SELECT
        //  ATS                 - response to RATS
        //  PPSR                - response to PPS
        //  STD Blocks (generated in parent class)
        //  Othrers - non valid messages for when we don't care about the contents

        // ====================================================================
        // User specified data
        // ====================================================================

        function TransType generate_from_byte_queue(logic [7:0] bq [$], int bits_in_first_byte=0);
            automatic ByteTransType trans = new(bq, bits_in_first_byte);
            if (bits_in_first_byte == 0) begin
                // add the CRC if we are auto-adding them
                append_crc(trans);
            end
            return convert_and_cast(trans);
        endfunction

        function TransType generate_from_byte_transaction(ByteTransType trans);
            // copy it, so we aren't just a reference to the original
            automatic ByteTransType res = new(trans.data, trans.bits_in_first_byte);

            if (res.bits_in_first_byte == 0) begin
                // add the CRC if we are auto-adding them
                append_crc(res);
            end
            return convert_and_cast(res);
        endfunction

        // ====================================================================
        // IOS/IEC 14443-3A messages
        // ====================================================================

        function TransType generate_atqa(ISO14443A_pkg::UIDSize uid_size);
            automatic logic [15:0]  ATQA_REPLY  = ISO14443A_pkg::ATQA(uid_size);
            automatic ByteTransType trans       = new('{ATQA_REPLY[7:0], ATQA_REPLY[15:8]});
            // this doesn't have a CRC
            return convert_and_cast(trans);
        endfunction

        function TransType generate_ac_reply(int uid_bits_sent, logic [31:0] uid);
            automatic ByteTransType     trans   = new;
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
            return convert_and_cast(trans);
            endfunction

        function TransType generate_sak(logic uid_complete);
            automatic ByteTransType trans = new;

            trans.push_back(uid_complete ? ISO14443A_pkg::SAK_UID_COMPLETE
                                         : ISO14443A_pkg::SAK_UID_NOT_COMPLETE);

            // add the CRC if we are auto-adding them
            append_crc(trans);
            return convert_and_cast(trans);
        endfunction

        // ====================================================================
        // IOS/IEC 14443-4A messages
        // ====================================================================

        function TransType generate_ats;
            // our ATS reply is just the TL field, which is the length including itself (= 1)
            automatic ByteTransType trans = new('{8'd1});

            // add the CRC if we are auto-adding them
            append_crc(trans);
            return convert_and_cast(trans);
        endfunction

        function TransType generate_ppsr (logic [3:0] cid);
            automatic ByteTransType trans = new;

            // The response to PPS is just the PPSS byte including the CID
            trans.data.push_back({ISO14443A_pkg::PPSS, cid});

            // add the CRC if we are auto-adding them
            append_crc(trans);
            return convert_and_cast(trans);
        endfunction

        // ====================================================================
        // IOS/IEC 14443-4 std blocks
        // ====================================================================
        // generated in the parent class TransactionGenerator

    endclass

endpackage
