/***********************************************************************
        File: tx_interface_source.sv
 Description: Source for the tx_interface
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

module tx_interface_source
(
    input                   clk,
    tx_interface.out_byte   iface
);

    function void initialise;
        iface.data_valid <= 0;
    endfunction

    // sends out a frame
    task send_frame (logic [iface.DATA_WIDTH-1:0] sq[$], int bits_in_first_byte=0);
        // bits_in_first_byte == 0 and == 8 are sort of the same thing
        // we allow both to be used here
        if (bits_in_first_byte == 8) begin
            bits_in_first_byte = 0;
        end

        // set bits for first byte
        iface.data_bits <= 3'(bits_in_first_byte);

        foreach (sq[i]) begin
            // set up the inputs
            iface.data          <= sq[i];
            iface.data_valid    <= 1'b1;

            // wait a tick so req isn't asserted still
            @(posedge clk)

            // wait for the next req, and align to the clock
            wait (iface.req) begin end
            @(posedge clk) begin end

            // all remaining bits have 8 bits per byte
            iface.data_bits = 3'd0;
        end

        // nothing more to send
        iface.data_valid <= 1'b0;
    endtask

endmodule
