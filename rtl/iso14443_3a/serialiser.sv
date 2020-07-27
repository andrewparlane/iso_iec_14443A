/***********************************************************************
        File: serialiser.sv
 Description: Convert a series of bytes into bits (tx path)
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

module serialiser
(
    // clk is our 13.56MHz input clock.
    input                   clk,

    // rst_n is our active low synchronised asynchronous reset signal
    input                   rst_n,

    // input data
    tx_interface.in_byte    in_iface,

    // output data
    tx_interface.out_bit    out_iface
);

    logic [7:0] cached_data;
    logic [2:0] bit_count;

    logic idle;
    logic cache_data;

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            in_iface.req            <= 1'b0;
            idle                    <= 1'b1;
        end
        else begin
            // these should only be asserted for at most one tick
            in_iface.req <= 1'b0;

            if (idle) begin
                // wait for in_iface.data_valid
                if (in_iface.data_valid) begin
                    idle            <= 1'b0;
                    cached_data     <= in_iface.data;
                    bit_count       <= in_iface.data_bits - 1'd1;
                    cache_data      <= 1'b0;
                end
            end
            else begin
                // wait for out_iface.req
                if (out_iface.req) begin
                    // if we repeatedly updating the data cache then stop now that we've got a new req
                    cache_data <= 1'b0;

                    // prepare next bit
                    if (bit_count == 0) begin
                        // need a new byte
                        in_iface.req    <= 1'b1;
                        bit_count       <= 3'd7;    // always 8 bits after the first byte

                        // we don't know exactly when it'll be ready
                        // so just keep caching it until upstream next requests a bit
                        cache_data      <= 1'b1;
                    end
                    else begin
                        // shift the cached data
                        cached_data[6:0]    <= cached_data[7:1];
                        bit_count           <= bit_count - 1'd1;
                    end
                end
                else if (cache_data) begin
                    // update the data cache
                    cached_data <= in_iface.data;

                    if (!in_iface.data_valid) begin
                        // nothing more to send
                        idle <= 1'b1;
                    end
                end
            end
        end
    end

    assign out_iface.data_valid         = !idle;
    assign out_iface.data               = cached_data[0];
    assign out_iface.last_bit_in_byte   = (bit_count == 0);

endmodule
