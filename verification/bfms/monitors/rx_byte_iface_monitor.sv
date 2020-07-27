/***********************************************************************
        File: rx_byte_iface_monitor.sv
 Description: A monitor for the rx_iface #(.BY_BYTE(1))
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

package rx_byte_iface_monitor_pkg;

    class RxByteIfaceMonitor
    extends rx_iface_monitor_pkg::RxIfaceMonitor
    #(
        .IfaceType  (virtual rx_interface #(.BY_BYTE(1))),
        .TransType  (rx_byte_transaction_pkg::RxMonitorByteTransaction)
    );

        function new (IfaceType _vif);
            super.new(_vif);
        endfunction

        // the only difference with the ByteIface is that we have to deal with partial bytes
        virtual protected function ResultCode handle_event(TransType trans);
            automatic ResultCode res = super.handle_event(trans);
            if (vif.eoc) begin
                // This is the EOC
                if (vif.data_valid) begin
                    // there was data, so it's a partial byte (or could be)
                    trans.bits_in_last_byte = vif.data_bits;
                end
                else begin
                    // there was no data, so we finished with a full byte
                    trans.bits_in_last_byte = 0;
                end
            end
            else if (vif.data_valid && (vif.data_bits != 0)) begin
                // not an EOC, and data is valid and data_bits != 0
                // this isn't valid, we only allow partial bytes on EOC
                return ResultCode_ERROR;
            end

            return res;
        endfunction

    endclass

endpackage
