/***********************************************************************
        File: routing.sv
 Description: Code to route messages based on the current state of initialisation
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

module routing
(
    // Control signals
    input                   route_rx_to_initialisation,
    input                   route_rx_to_14443_4,
    input                   route_tx_from_14443_4,

    // Rx interfaces
    rx_interface.in_byte    in_rx_iface,
    rx_interface.out_byte   out_rx_iface_init,
    rx_interface.out_byte   out_rx_iface_14443_4,

    // Tx interfaces
    tx_interface.in_byte    in_tx_iface_init,
    input                   in_tx_append_crc_init,
    tx_interface.in_byte    in_tx_iface_14443_4,
    input                   in_tx_append_crc_14443_4,
    tx_interface.out_byte   out_tx_iface,
    output logic            out_tx_append_crc
);

    // Do this with combinatory logic so there's no delay, and uses less area.
    // Our clock is 13.56MHz, so timing shouldn't be an issue.
    // Additionally glitches shouldn't be an issue, since all are active high
    // and the route_to_... signals only change outside of frames.
    // TODO: Check if this is actually OK.

    // ========================================================================
    // Rx
    // ========================================================================

    assign out_rx_iface_init.data           = in_rx_iface.data;
    assign out_rx_iface_init.data_bits      = in_rx_iface.data_bits;
    assign out_rx_iface_init.error          = in_rx_iface.error         && route_rx_to_initialisation;
    assign out_rx_iface_init.soc            = in_rx_iface.soc           && route_rx_to_initialisation;
    assign out_rx_iface_init.eoc            = in_rx_iface.eoc           && route_rx_to_initialisation;
    assign out_rx_iface_init.data_valid     = in_rx_iface.data_valid    && route_rx_to_initialisation;

    assign out_rx_iface_14443_4.data        = in_rx_iface.data;
    assign out_rx_iface_14443_4.data_bits   = in_rx_iface.data_bits;
    assign out_rx_iface_14443_4.error       = in_rx_iface.error         && route_rx_to_14443_4;
    assign out_rx_iface_14443_4.soc         = in_rx_iface.soc           && route_rx_to_14443_4;
    assign out_rx_iface_14443_4.eoc         = in_rx_iface.eoc           && route_rx_to_14443_4;
    assign out_rx_iface_14443_4.data_valid  = in_rx_iface.data_valid    && route_rx_to_14443_4;

    // ========================================================================
    // Tx
    // ========================================================================

    always_comb begin
        if (route_tx_from_14443_4) begin
            out_tx_iface.data       = in_tx_iface_14443_4.data;
            out_tx_iface.data_valid = in_tx_iface_14443_4.data_valid;
            out_tx_iface.data_bits  = in_tx_iface_14443_4.data_bits;
            in_tx_iface_14443_4.req = out_tx_iface.req;
            in_tx_iface_init.req    = 1'b0;
            out_tx_append_crc       = in_tx_append_crc_14443_4;
        end
        else begin
            out_tx_iface.data       = in_tx_iface_init.data;
            out_tx_iface.data_valid = in_tx_iface_init.data_valid;
            out_tx_iface.data_bits  = in_tx_iface_init.data_bits;
            in_tx_iface_init.req    = out_tx_iface.req;
            in_tx_iface_14443_4.req = 1'b0;
            out_tx_append_crc       = in_tx_append_crc_init;
        end
    end

endmodule
