/***********************************************************************
        File: tx_bit_iface_monitor.sv
 Description: A generic monitor for Tx interfaces with BY_BYTE = 0
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

package tx_bit_iface_monitor_pkg;

    class TxBitIfaceMonitor
    extends tx_iface_monitor_pkg::TxIfaceMonitor
    #(
        .IfaceType  (virtual tx_interface #(.BY_BYTE(0))),
        .TransType  (tx_bit_transaction_pkg::TxBitTransaction)
    );

        function new (IfaceType _vif);
            super.new(_vif);
        endfunction

        // we could verify the behaviour of last_bit_in_byte here
        // but ignoring this for now

        /* virtual protected function sample_data(TransType trans);
            super.sample_data(trans);
            // first must assert within 8 bits - and record first_bits_in_byte
            // must assert every 8 bits after that
        endfunction

        virtual protected task process(output TransType trans, output logic res);
            super.process(trans, res);
            // we could check that trans.data.size() == first_bits_in_byte
        end */
    endclass

endpackage
