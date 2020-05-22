/***********************************************************************
        File: tx_bit_iface_source_driver.sv
 Description: A driver for the source of the tx_iface #(.BY_BYTE(0))
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

package tx_bit_iface_source_driver_pkg;

    class TxBitIfaceSourceDriver
    extends tx_iface_source_driver_pkg::TxIfaceSourceDriver
    #(
        .IfaceType  (virtual tx_interface #(.BY_BYTE(0))),
        .TransType  (tx_bit_transaction_pkg::TxBitTransaction)
    );

        protected int current_bit_count;

        function new (IfaceType _vif,
                      int _idle_ticks_after_transaction = 32,
                      int _req_timeout                  = 32,
                      int _first_req_timeout            = _req_timeout);

            super.new(_vif, _idle_ticks_after_transaction,
                      _req_timeout, _first_req_timeout);

        endfunction

        virtual protected task send_data_elem(TransType trans, int idx);
            super.send_data_elem(trans, idx);

            // set the last_bit_in_byte signal
            vif.last_bit_in_byte <= (current_bit_count == 7);
            current_bit_count = (current_bit_count + 1) % 8;
        endtask

        // override send_data so we can calculate our initial current_bit_count
        // so we can correctly set vif.last_bit_in_byte
        virtual protected task send_data(TransType trans);
            // if trans.data.size() % 8 is not 0, then we are sending data with a partial first byte
            automatic int bits_in_first_byte = trans.data.size() % 8;

            // so vif.last_bit_in_byte is set in bits_in_first_byte bits
            // the exception being when bits_in_first_byte == 0 (full byte).
            current_bit_count = (bits_in_first_byte == 0) ? 0 : (8 - bits_in_first_byte);

            // pass it on to the parent class to do the actual sending
            super.send_data(trans);

            // all Tx transactions should end with last_bit_in_byte asserted
            // unless it timedout.
            lastBitInByteSet:
            assert (vif.last_bit_in_byte || timedout) else $error("last_bit_in_byte not set at the end of transaction");

            // finally deassert last_bit_in_byte
            vif.last_bit_in_byte <= 1'b0;
        endtask
    endclass

endpackage
