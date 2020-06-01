/***********************************************************************
        File: rx_bit_transaction_generator.sv
 Description: class for generation of Rx Bit transactions
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

package rx_bit_transaction_generator_pkg;

    class RxBitTransactionGenerator
    #(
        // must extend QueueTransaction
        type TransType = rx_bit_transaction_pkg::RxBitTransaction
    )
    extends rx_transaction_generator_pkg::RxTransactionGenerator
    #(
        .TransType  (TransType)
    );

        typedef rx_bit_transaction_pkg::RxBitTransaction NativeTransType;

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
