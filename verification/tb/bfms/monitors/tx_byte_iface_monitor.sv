/***********************************************************************
        File: tx_byte_iface_monitor.sv
 Description: A generic monitor for all Tx interfaces with BY_BYTE = 1
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

package tx_byte_iface_monitor_pkg;

    class TxByteIfaceMonitor
    extends tx_iface_monitor_pkg::TxIfaceMonitor
    #(
        .IfaceType  (virtual tx_interface #(.BY_BYTE(1))),
        .TransType  (tx_byte_transaction_pkg::TxByteTransaction)
    );

        function new (IfaceType _vif);
            super.new(_vif);
        endfunction

        virtual protected function void sample_data(TransType trans);
            // if this is the first byte sample data_bits
            // otherwise assert that it's a full byte
            if (trans.data.size() == 0) begin: firstByte
                trans.bits_in_first_byte = vif.data_bits;
            end
            else begin: notFirstByte
                fullByte:
                assert(vif.data_bits == 0) else $error("data_bits is %d for not the first byte", vif.data_bits);
            end

            super.sample_data(trans);
        endfunction

    endclass

endpackage
