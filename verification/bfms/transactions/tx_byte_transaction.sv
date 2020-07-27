/***********************************************************************
        File: tx_byte_transaction.sv
 Description: Transactions for use with the various drivers
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

package tx_byte_transaction_pkg;

    import transaction_pkg::*;
    import queue_transaction_pkg::*;

    class TxByteTransaction
    extends queue_transaction_pkg::ByteQueueTransaction;

        // can have partial byte on the first byte (AC response)
        int bits_in_first_byte;

        function new (logic [7:0] _data [$] = '{}, int _bits_in_first_byte = 0);
            super.new(_data);
            bits_in_first_byte = _bits_in_first_byte;
        endfunction

        static function TxByteTransaction new_random_transaction (int num_bytes, int _bits_in_first_byte=-1);
            automatic TxByteTransaction res = new();
            res.fill_with_random(num_bytes);
            res.bits_in_first_byte = (_bits_in_first_byte == -1) ? $urandom_range(7)
                                                                : _bits_in_first_byte;
            return res;
        endfunction

        static function TxByteTransaction new_random_transaction_bits (int num_bits);
            automatic TxByteTransaction res = new();
            automatic int               num_bytes = int'($ceil(num_bits / 8.0));

            // transactions with partial bytes have int'($ceil(num_bits / 8)) bytes
            // the first of which is partial and has (num_bits % 8) bits

            res.fill_with_random(num_bytes);
            res.bits_in_first_byte = num_bits % 8;
            return res;
        endfunction

        virtual function void append_crc;
            fullBytes: assert(bits_in_first_byte == 0) else $fatal(0, "Can't add CRC to transactions with bits_in_first_byte != 0");
            super.append_crc;
        endfunction

        // can be used with BitQueueTransaction::new()
        function BitQueue convert_to_bit_queue;
            automatic BitQueue      res         = '{};
            automatic logic [7:0]   first_byte;

            if (bits_in_first_byte != 0) begin
                // temporarily pop the first byte off the queue
                first_byte = data.pop_front;

                // and add the partial byte to the queue
                for (int i = 0; i < bits_in_first_byte; i++) begin
                    res.push_back(first_byte[i]);
                end
            end

            res = {res, super.convert_to_bit_queue};

            if (bits_in_first_byte != 0) begin
                // restore our queue to the original
                data.push_front(first_byte);
            end

            return res;
        endfunction

        virtual function logic compare (Transaction rhs);
            automatic TxByteTransaction _rhs;
            if (!$cast(_rhs, rhs)) begin
                $fatal(0, "$cast failed");
            end

            if (bits_in_first_byte != _rhs.bits_in_first_byte) begin
                return 1'b0;
            end

            if (bits_in_first_byte != 0) begin
                automatic logic [7:0] our_first_byte;
                automatic logic [7:0] rhs_first_byte;

                // can't just compare the data as is, we need to deal with the first bytes separately
                // first check the lengths are the same
                if (data.size != _rhs.data.size) begin
                    return 1'b0;
                end

                // make sure there's at least 1 byte (can't pop the first byte if length is 0)
                // if this is a 0 byte frame, we shouldn't see bits_in_first_byte being none 0
                // but better to be sure.
                if (data.size == 0) begin
                    // they are both empty, so they match
                    return 1'b1;
                end

                // compare all the data except the first bytes
                if ((data.size != 1) && (data[1:$] != _rhs.data[1:$])) begin
                    return 1'b1;
                end

                // finally compare the first bytes
                our_first_byte = data[0];
                rhs_first_byte = _rhs.data[0];

                // clear the invalid MSbs
                for (int i = 7; i >= bits_in_first_byte; i--) begin
                    our_first_byte[i] = 1'b0;
                    rhs_first_byte[i] = 1'b0;
                end

                return our_first_byte == rhs_first_byte;
            end
            else begin
                return super.compare(rhs);
            end
        endfunction

        virtual function string to_string;
            return {super.to_string, $sformatf(", bits_in_first_byte: %d", bits_in_first_byte)};
        endfunction
    endclass

    // there's no need for a TxMonitorByteTransaction because there's no extra error signal

endpackage
