/***********************************************************************
        File: tx_byte_iface_source_driver.sv
 Description: A driver for the tx_iface #(.BY_BYTE(1))
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

package tx_byte_iface_source_driver_pkg;

    class TxByteIfaceSourceDriver
    extends tx_iface_source_driver_pkg::TxIfaceSourceDriver
    #(
        .IfaceType  (virtual tx_interface #(.BY_BYTE(1))),
        .TransType  (tx_byte_transaction_pkg::TxByteTransaction)
    );

        function new (IfaceType _vif,
                      int _idle_ticks_after_transaction = 32,
                      int _req_timeout                  = 32,
                      int _first_req_timeout            = _req_timeout);

            super.new(_vif, _idle_ticks_after_transaction,
                      _req_timeout, _first_req_timeout);

        endfunction

        virtual protected task send_data_elem(TransType trans, int idx);
            super.send_data_elem(trans, idx);
            // set data_bits
            vif.data_bits <= (idx == 0) ? trans.bits_in_first_byte : 3'b0;
        endtask

    endclass

endpackage
