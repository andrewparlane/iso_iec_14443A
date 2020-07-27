/***********************************************************************
        File: rx_byte_iface_driver.sv
 Description: A driver for the rx_iface #(.BY_BYTE(1))
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

package rx_byte_iface_driver_pkg;

    class RxByteIfaceDriver
    extends rx_iface_driver_pkg::RxIfaceDriver
    #(
        .IfaceType  (virtual rx_interface #(.BY_BYTE(1))),
        .TransType  (rx_byte_transaction_pkg::RxByteTransaction)
    );

        local logic [7:0] last_byte;

        function new (IfaceType _vif);
            super.new(_vif);
        endfunction

        // override the process task to remove the last byte if it's a partial byte
        // we also handle vif.num_bits for all but any partial last bytes
        virtual protected task process(TransType trans);
            // all bytes are full bytes with the potential exception of the last
            // which is sent on the EOC.
            vif.data_bits <= 3'b0;

            if (trans.bits_in_last_byte != 0) begin
                // if the queue is empty then trans.bits_in_last_byte should be 0
                // so we don't bother checking, and if it happens there will be an error
                // on the pop_back()
                last_byte = trans.pop_back();
            end

            // now let the parent handle the rest
            super.process(trans);
        endtask

        // override the send_eoc task so we can send our partial byte
        virtual protected task send_eoc(TransType trans);
            if (trans.bits_in_last_byte != 0) begin
                vif.data_valid  <= 1'b1;
                vif.data        <= last_byte;
                vif.data_bits   <= trans.bits_in_last_byte;
            end
            super.send_eoc(trans);
            vif.data_valid      <= 1'b0;
        endtask

    endclass

endpackage
