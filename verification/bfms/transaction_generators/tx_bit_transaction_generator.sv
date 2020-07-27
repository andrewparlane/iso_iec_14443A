/***********************************************************************
        File: tx_bit_transaction_generator.sv
 Description: class for generation of Tx Bit transactions
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

package tx_bit_transaction_generator_pkg;

    class TxBitTransactionGenerator
    #(
        // must extend QueueTransaction
        type TransType = tx_bit_transaction_pkg::TxBitTransaction
    )
    extends tx_transaction_generator_pkg::TxTransactionGenerator
    #(
        .TransType  (TransType)
    );

        typedef tx_bit_transaction_pkg::TxBitTransaction NativeTransType;

        protected logic auto_add_parity;

        function new (logic _auto_add_crc, logic _auto_add_parity);
            super.new(_auto_add_crc);
            auto_add_parity = _auto_add_parity;
        endfunction

        virtual protected function BaseTransType convert(ByteTransType trans);
            automatic NativeTransType res = new(trans.convert_to_bit_queue);

            // add parity bits if required
            if (auto_add_parity) begin
                res.add_parity;
            end

            return res;
        endfunction

    endclass

endpackage
