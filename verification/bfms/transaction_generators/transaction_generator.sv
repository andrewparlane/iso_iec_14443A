/***********************************************************************
        File: transaction_generator.sv
 Description: Base class for generation of Rx / Tx transactions
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

package transaction_generator_pkg;

    import std_block_address_pkg::StdBlockAddress;

    virtual class TransactionGenerator
    #(
        type TransType,     // must extend QueueTransaction
        type ByteTransType  // must be RxByteTransaction or TxByteTransaction
    );

        // BaseTransType is the base class of all Transactions
        typedef transaction_pkg::Transaction BaseTransType;

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

        virtual function void append_crc(ByteTransType trans);
            if (auto_append_crc) begin
                trans.append_crc;
                if (corrupt_crc) begin
                    automatic int corrupt_crc_byte  = $urandom_range(1);
                    automatic int corrupt_crc_bit   = $urandom_range(7);

                    trans.data[$-corrupt_crc_byte][corrupt_crc_bit] = !trans.data[$-corrupt_crc_byte][corrupt_crc_bit];
                end
            end
        endfunction

        // this class and any child class can have generate_X functions that generate TransType
        // transactions. They should generate the transaction first as a ByteTransType byte_trans
        // (Rx/TxByteTransaction), then return convert_and_cast(byte_trans).
        //
        // convert_and_cast() calls convert() on the passed transaction which being a virtual
        // function is called on the child class, it converts the ByteTransType transaction to
        // whatever transaction type is native for that class, but returns it as a BaseTransType
        // Finally convert_and_cast() casts that to TransType.

        // It may seem convoluted, but it allows us to reuse message generation code and receive
        // transactions of the correct type, without having to worry about the conversion / casting
        // in the testbenches.

        // must be overridden
        pure virtual protected function BaseTransType convert(ByteTransType trans);

        virtual protected function TransType convert_and_cast(ByteTransType trans);
            automatic BaseTransType tmp = convert(trans);
            automatic TransType     res;

            castOK:
            assert ($cast(res, tmp)) else $fatal(0, "Cast to TransType failed");

            return res;
        endfunction

        // must be overridden
        pure virtual protected function logic is_rx_trans_gen;

        // ====================================================================
        // IOS/IEC 14443-4 std blocks
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

        protected function TransType generate_std_block (StdBlockAddress addr, logic [7:0] pcb, logic [7:0] inf [$] = '{});
            automatic ByteTransType trans = new;

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
                automatic logic [1:0] power = is_rx_trans_gen() ? 2'b00 : addr.power;

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
            return convert_and_cast(trans);
        endfunction

        function TransType generate_std_i_block (StdBlockAddress addr, logic chaining, logic block_num, logic [7:0] inf [$]);
            automatic logic [7:0] pcb = {3'b000, chaining, 3'b001, block_num};
            return generate_std_block(addr, pcb, inf);
        endfunction

        function TransType generate_std_r_block (StdBlockAddress addr, logic nak, logic block_num);
            automatic logic [7:0] pcb = {3'b101, nak, 3'b001, block_num};
            return generate_std_block(addr, pcb);
        endfunction

        function TransType generate_std_r_ack(StdBlockAddress addr, logic block_num);
            return generate_std_r_block(addr, 1'b0, block_num);
        endfunction

        function TransType generate_std_r_nak(StdBlockAddress addr, logic block_num);
            return generate_std_r_block(addr, 1'b1, block_num);
        endfunction

        function TransType generate_std_s_block (StdBlockAddress addr, logic [1:0] b6_5, logic b2, logic [7:0] inf [$] = '{});
            automatic logic [7:0] pcb = {2'b11, b6_5, 2'b00, b2, 1'b0};
            return generate_std_block(addr, pcb, inf);
        endfunction

        function TransType generate_std_s_deselect(StdBlockAddress addr);
            return generate_std_s_block(addr, 2'b00, 1'b1);
        endfunction

        function TransType generate_std_s_parameters(StdBlockAddress addr, logic [7:0] inf [$]);
            return generate_std_s_block(addr, 2'b11, 1'b0, inf);
        endfunction

    endclass

endpackage
