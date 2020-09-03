/***********************************************************************
        File: rx_transaction_converter.sv
 Description: Base class for conversion of Rx transactions
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

package rx_transaction_converter_pkg;

    import transaction_converter_pkg::*;

    import rx_byte_transaction_pkg::*;
    import rx_bit_transaction_pkg::*;
    import pcd_pause_n_transaction_pkg::*;

    // The sequences create RxByteTransactions but the RxDrivers use RxByteTransactions
    // or RxBitTransactions or PCDPauseNTransaction depending on which driver we use.
    // These converter classes let the Sequence class contain a TransactionConverter member
    // that is instantiated with the appropriate version of the converter to convert the
    // RxByteTransactions into the needed format.

    // ====================================================================
    // Byte -> Byte (identity)
    // ====================================================================

    class RxByteToByteTransactionConverter
    extends TransactionConverter
    #(
        .InputTransType     (RxByteTransaction),
        .OutputTransType    (RxByteTransaction)
    );

        virtual virtual function OutputTransType convert(InputTransType trans);
            // do nothing
            return trans;
        endfunction

    endclass

    // ====================================================================
    // Byte -> Bit
    // ====================================================================

    class RxByteToBitTransactionConverter
    extends TransactionConverter
    #(
        .InputTransType     (RxByteTransaction),
        .OutputTransType    (RxBitTransaction)
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

    // ====================================================================
    // Bit -> PCD pause_n
    // ====================================================================

    class RxBitToPCDPauseNTransactionConverter
    extends TransactionConverter
    #(
        .InputTransType     (RxBitTransaction),
        .OutputTransType    (PCDPauseNTransaction)
    );

        virtual virtual function OutputTransType convert(InputTransType trans);
            automatic OutputTransType res = new(trans.convert_to_pcd_sequence_queue);
            return res;
        endfunction

    endclass

    // ====================================================================
    // Byte -> PCD pause_n
    // ====================================================================

    class RxByteToPCDPauseNTransactionConverter
    extends TransactionConverter
    #(
        .InputTransType     (RxByteTransaction),
        .OutputTransType    (PCDPauseNTransaction)
    );

        protected RxByteToBitTransactionConverter       byte_to_bit;
        protected RxBitToPCDPauseNTransactionConverter  bit_to_pcd_pause_n;

        function new (logic _auto_add_parity);
            byte_to_bit         = new(_auto_add_parity);
            bit_to_pcd_pause_n  = new;
        endfunction

        virtual virtual function OutputTransType convert(InputTransType trans);
            return bit_to_pcd_pause_n.convert(byte_to_bit.convert(trans));
        endfunction

    endclass

endpackage
