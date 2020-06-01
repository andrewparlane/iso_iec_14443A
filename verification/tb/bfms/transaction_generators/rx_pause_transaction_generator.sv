/***********************************************************************
        File: rx_pause_transaction_generator.sv
 Description: class for generation of PCDPauseN transactions
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

package rx_pause_transaction_generator_pkg;

    class RxPauseTransactionGenerator
    #(
        type TransType = pcd_pause_n_transaction_pkg::PCDPauseNTransaction
    )
    extends rx_bit_transaction_generator_pkg::RxBitTransactionGenerator
    #(
        .TransType  (TransType)
    );

        typedef rx_bit_transaction_pkg::RxBitTransaction            ParentTransType;
        typedef pcd_pause_n_transaction_pkg::PCDPauseNTransaction   NativeTransType;

        function new (logic _auto_add_crc, logic _auto_add_parity);
            super.new(_auto_add_crc, _auto_add_parity);
        endfunction

        virtual protected function BaseTransType convert(ByteTransType trans);
            automatic ParentTransType   bit_trans;
            automatic NativeTransType   res;

            // Get our parent to convert it to an RxBitTransaction (returned as BaseTransType
            // so we need to cast it)
            castOK: assert($cast(bit_trans, super.convert(trans)))
                else $fatal(0, "Failed to cast Transaction to RxBitTransaction");

            // convert the bit queue to a sequence queue
            res = new (bit_trans.convert_to_pcd_sequence_queue);
            return res;
        endfunction

    endclass

endpackage
