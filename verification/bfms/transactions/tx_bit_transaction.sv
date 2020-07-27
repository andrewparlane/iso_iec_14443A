/***********************************************************************
        File: tx_bit_transaction.sv
 Description: Transaction for the Tx bit interface
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

package tx_bit_transaction_pkg;

    import transaction_pkg::*;
    import queue_transaction_pkg::*;

    class TxBitTransaction
    extends queue_transaction_pkg::BitQueueTransaction;

        function new (logic _data [$] = '{});
            super.new(_data);
        endfunction

        static function TxBitTransaction new_random_transaction (int num_bits);
            automatic TxBitTransaction res = new();
            res.fill_with_random(num_bits);
            return res;
        endfunction

        // we ignore the argument, it has to be there because SV doesn't support overloading
        // functions, and add_parity in the BitQueueTransaction has an argument for the
        // number of bits in the first byte.
        virtual function void add_parity(int bits_in_first_byte=8);
            super.add_parity(data.size() % 8);
        endfunction

    endclass

    // there's no need for a TxMonitorBitTransaction because there's no extra error signal

endpackage
