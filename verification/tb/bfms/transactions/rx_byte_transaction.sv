/***********************************************************************
        File: rx_byte_transaction.sv
 Description: Transactions for use with the various drivers
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

package rx_byte_transaction_pkg;

    import transaction_pkg::*;
    import queue_transaction_pkg::*;

    class RxByteTransaction
    extends queue_transaction_pkg::ByteQueueTransaction;

        // can have partial byte on the last byte
        int bits_in_last_byte;

        function new (logic [7:0] _data [$] = '{}, int _bits_in_last_byte = 0);
            super.new(_data);
            bits_in_last_byte = _bits_in_last_byte;
        endfunction

        static function RxByteTransaction new_random_transaction (int num_bytes, int _bits_in_last_byte=-1);
            automatic RxByteTransaction res = new();
            res.fill_with_random(num_bytes);
            res.bits_in_last_byte = (_bits_in_last_byte == -1) ? $urandom_range(7)
                                                               : _bits_in_last_byte;
            return res;
        endfunction

        static function RxByteTransaction new_random_transaction_bits (int num_bits);
            automatic RxByteTransaction res = new();
            automatic int               num_bytes = int'($ceil(num_bits / 8.0));

            // transactions with partial bytes have int'($ceil(num_bits / 8)) bytes
            // the last of which is partial and has (num_bits % 8) bits

            res.fill_with_random(num_bytes);
            res.bits_in_last_byte = num_bits % 8;
            return res;
        endfunction

        virtual function void append_crc;
            fullBytes: assert(bits_in_last_byte == 0) else $fatal(0, "Can't add CRC to transactions with bits_in_last_byte != 0");
            super.append_crc;
        endfunction

        // can be used with BitQueueTransaction::new()
        function BitQueue convert_to_bit_queue;
            automatic BitQueue      res;
            automatic logic [7:0]   last_byte;

            if (bits_in_last_byte != 0) begin
                // temporarily pop the last byte off the queue
                last_byte = data.pop_back;
            end

            res = super.convert_to_bit_queue;

            if (bits_in_last_byte != 0) begin
                // restore our queue to the original
                data.push_back(last_byte);

                // and add the partial byte to the queue
                for (int i = 0; i < bits_in_last_byte; i++) begin
                    res.push_back(last_byte[i]);
                end
            end

            return res;
        endfunction

        virtual function logic compare (Transaction rhs);
            automatic RxByteTransaction _rhs;
            if (!$cast(_rhs, rhs)) begin
                $fatal(0, "$cast failed");
            end

            if (bits_in_last_byte != _rhs.bits_in_last_byte) begin
                return 1'b0;
            end

            if (bits_in_last_byte != 0) begin
                automatic logic [7:0] our_last_byte;
                automatic logic [7:0] rhs_last_byte;

                // can't just compare the data as is, we need to deal with the last bytes separately
                // first check the lengths are the same
                if (data.size != _rhs.data.size) begin
                    return 1'b0;
                end

                // make sure there's at least 1 byte (can't pop the last byte if length is 0)
                // if this is a 0 byte frame, we shouldn't see bits_in_last_byte being none 0
                // but better to be sure.
                if (data.size == 0) begin
                    // they are both empty, so they match
                    return 1'b1;
                end

                // compare all the data except the last bytes
                if ((data.size != 1) && (data[0:$-1] != _rhs.data[0:$-1])) begin
                    return 1'b1;
                end

                // finally compare the last bytes
                our_last_byte = data[$];
                rhs_last_byte = _rhs.data[$];

                // clear the invalid MSbs
                for (int i = 7; i >= bits_in_last_byte; i--) begin
                    our_last_byte[i] = 1'b0;
                    rhs_last_byte[i] = 1'b0;
                end

                return our_last_byte == rhs_last_byte;
            end
            else begin
                return super.compare(rhs);
            end
        endfunction

        virtual function string to_string;
            return {super.to_string, $sformatf(", bits_in_last_byte: %d", bits_in_last_byte)};
        endfunction
    endclass

    class RxMonitorByteTransaction
    extends RxByteTransaction;
        logic error;

        function new (logic [7:0] _data [$] = '{}, int _bits_in_last_byte = 0, logic _error = 1'b0);
            super.new(_data, _bits_in_last_byte);
            error = _error;
        endfunction

        static function RxMonitorByteTransaction new_random_transaction (int num_bytes, int _bits_in_last_byte=-1, int _error=-1);
            automatic RxMonitorByteTransaction res = new();
            res.fill_with_random(num_bytes);
            res.bits_in_last_byte   = (_bits_in_last_byte == -1) ? $urandom_range(7)
                                                                 : _bits_in_last_byte;
            res.error               = (_error == -1) ? 1'($urandom) : 1'(_error);
            return res;
        endfunction

        static function RxMonitorByteTransaction new_random_transaction_bits (int num_bits, int _error = -1);
            automatic RxMonitorByteTransaction  res = new();
            automatic int                       num_bytes = int'($ceil(num_bits / 8.0));

            // transactions with partial bytes have int'($ceil(num_bits / 8)) bytes
            // the last of which is partial and has (num_bits % 8) bits

            res.fill_with_random(num_bytes);
            res.bits_in_last_byte   = num_bits % 8;
            res.error               = (_error == -1) ? 1'($urandom) : 1'(_error);
            return res;
        endfunction

        static function RxMonitorByteTransaction create_from_rx_byte_transaction (RxByteTransaction rhs, logic _error = 1'b0);
            automatic RxMonitorByteTransaction res = new(rhs.data, rhs.bits_in_last_byte, _error);
            return res;
        endfunction

        virtual function logic compare (Transaction rhs);
            automatic RxMonitorByteTransaction _rhs;
            if (!$cast(_rhs, rhs)) begin
                $fatal(0, "$cast failed");
            end

            // if we got an error but weren't expecting one
            // or if we expected an error but didn't get one
            // then the transactions aren't equal
            if (error != _rhs.error) begin
                return 1'b0;
            end

            // if we detected an error then ignore the data and count the frames as equal
            if (error) begin
                return 1'b1;
            end

            // otherwise ...
            return super.compare(rhs);
        endfunction

        virtual function string to_string;
            return {super.to_string, $sformatf(", error: %b", error)};
        endfunction
    endclass

endpackage
