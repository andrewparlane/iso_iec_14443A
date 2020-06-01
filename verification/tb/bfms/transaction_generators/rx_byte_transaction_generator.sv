/***********************************************************************
        File: rx_byte_transaction_generator.sv
 Description: class for generation of Rx Byte transactions
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

package rx_byte_transaction_generator_pkg;

    class RxByteTransactionGenerator
    #(
        // must extend QueueTransaction
        type TransType = rx_byte_transaction_pkg::RxByteTransaction
    )
    extends rx_transaction_generator_pkg::RxTransactionGenerator
    #(
        .TransType  (TransType)
    );

        typedef ByteTransType NativeTransType;

        function new (logic _auto_add_crc);
            super.new(_auto_add_crc);
        endfunction

        virtual protected function BaseTransType convert(ByteTransType trans);
            // NativeTransType == ByteTransType
            return trans;
        endfunction

    endclass

endpackage
