/***********************************************************************
        File: rx_transaction_generator.sv
 Description: Base class for generation of Rx transactions
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

package rx_transaction_generator_pkg;

    virtual class RxTransactionGenerator
    #(
        type TransType  // must extend QueueTransaction
    )
    extends transaction_generator_pkg::TransactionGenerator
    #(
        .TransType      (TransType),
        .ByteTransType  (rx_byte_transaction_pkg::RxByteTransaction)
    );

        // We generate everything as RxByteTransaction by default, child classes then convert
        // this to their own transaction format

        function new (logic _auto_append_crc);
            super.new(_auto_append_crc);
        endfunction

        virtual protected function logic is_rx_trans_gen;
            return 1'b1;
        endfunction

        // PCD -> PICC messages are:
        //  REQA
        //  WUPA
        //  HLTA
        //  SELECT/AC
        //  RATS
        //  PPS
        //  STD Blocks (generated in parent class)
        //  Othrers - non valid messages that we want to check the PICC doesn't respond to

        // ====================================================================
        // Constrained random
        // ====================================================================

        // random transaction that should not be accepted as any valid 14443-3A or 14443-4A Rx frames.
        function TransType generate_random_non_valid(int num_bytes);
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

            return generate_from_byte_queue(bq, 0);
        endfunction

        // ====================================================================
        // User specified data
        // ====================================================================

        function TransType generate_from_byte_queue(logic [7:0] bq [$], int bits_in_last_byte=0);
            automatic ByteTransType trans = new(bq, bits_in_last_byte);
            if (bits_in_last_byte == 0) begin
                // add the CRC if we are auto-adding them
                append_crc(trans);
            end
            return convert_and_cast(trans);
        endfunction

        // ====================================================================
        // IOS/IEC 14443-3A messages
        // ====================================================================

        function TransType generate_reqa;
            automatic ByteTransType trans = new('{{1'($urandom), ISO14443A_pkg::REQA}}, 7);
            // this doesn't have a CRC because it's only 7 bits
            return convert_and_cast(trans);
        endfunction

        function TransType generate_wupa;
            automatic ByteTransType trans = new('{{1'($urandom), ISO14443A_pkg::WUPA}}, 7);
            // this doesn't have a CRC because it's only 7 bits
            return convert_and_cast(trans);
        endfunction

        function TransType generate_hlta;
            automatic ByteTransType trans = new('{ISO14443A_pkg::HLTA[7:0], ISO14443A_pkg::HLTA[15:8]});
            // add the CRC if we are auto-adding them
            append_crc(trans);
            return convert_and_cast(trans);
        endfunction

        // ANTI COLLISION / SELECT
        function TransType generate_ac_select(int level, int uid_bits, logic [31:0] uid, logic toggle_last_bcc_bit = 1'b0);
            automatic ByteTransType trans = new;

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

            return convert_and_cast(trans);
        endfunction

        // ====================================================================
        // IOS/IEC 14443-4A messages
        // ====================================================================

        function TransType generate_rats (logic [3:0] fsdi, logic [3:0] cid);
            automatic ByteTransType trans = new;

            trans.push_back(ISO14443A_pkg::RATS);
            trans.push_back({fsdi, cid});

            // add the CRC if we are auto-adding them
            append_crc(trans);
            return convert_and_cast(trans);
        endfunction

        function TransType generate_pps (logic [3:0] cid, logic p1_present, logic [1:0] dsi, logic [1:0] dri);
            automatic ByteTransType trans = new;

            trans.push_back({ISO14443A_pkg::PPSS, cid});       // PPSS
            trans.push_back({3'b000, p1_present, 4'b0001});    // PPS0
            if (p1_present) begin
                trans.push_back({4'b0000, dsi, dri});          // PPS1
            end

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
