/***********************************************************************
        File: rx_bit_iface_driver.sv
 Description: A driver for the rx_iface #(.BY_BYTE(0))
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

package rx_bit_iface_driver_pkg;

    class RxBitIfaceDriver
    extends rx_iface_driver_pkg::RxIfaceDriver
    #(
        .IfaceType  (virtual rx_interface #(.BY_BYTE(0))),
        .TransType  (rx_bit_transaction_pkg::RxBitTransaction)
    );

        function new (IfaceType _vif);
            super.new(_vif);
        endfunction

    endclass

endpackage
