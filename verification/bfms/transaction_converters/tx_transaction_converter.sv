/***********************************************************************
        File: tx_transaction_converter.sv
 Description: Base class for conversion of Tx transactions
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

package tx_transaction_converter_pkg;

    import transaction_converter_pkg::*;

    import tx_byte_transaction_pkg::*;
    import tx_bit_transaction_pkg::*;

    // The sequences create TxByteTransactions but the TxMonitors produce TxByteTransactions
    // or TxBitTransactions depending on which monitor we use. These converter classes
    // let the Sequence class contain a TransactionConverter member that is instantiated
    // with the appropriate version of the converter to convert the TxByteTransactions into
    // the needed format.

    // ====================================================================
    // Byte -> Byte (identity)
    // ====================================================================

    class TxByteToByteTransactionConverter
    extends TransactionConverter
    #(
        .InputTransType     (TxByteTransaction),
        .OutputTransType    (TxByteTransaction)
    );

        virtual virtual function OutputTransType convert(InputTransType trans);
            // do nothing
            return trans;
        endfunction

    endclass

    // ====================================================================
    // Byte -> Bit
    // ====================================================================

    class TxByteToBitTransactionConverter
    extends TransactionConverter
    #(
        .InputTransType     (TxByteTransaction),
        .OutputTransType    (TxBitTransaction)
    );

        protected logic auto_add_parity;

        function new (logic _auto_add_parity);
            auto_add_parity = _auto_add_parity;
        endfunction

        virtual virtual function OutputTransType convert(InputTransType trans);
            automatic OutputTransType res = new(trans.convert_to_bit_queue);

            // add parity bits if required
            if (auto_add_parity) begin
                res.add_parity;
            end

            return res;
        endfunction

    endclass

endpackage
