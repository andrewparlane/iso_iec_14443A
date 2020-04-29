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
    tx_interface.out_all    iface
);
    logic initialise_called = 1'b0;

    function void initialise;
        iface.data_valid    <= 0;
        initialise_called   <= 1'b1;
    endfunction

    initial begin: initialiseCalledCheck
        repeat(2) @(posedge clk) begin end
        initialiseCalled:
            assert (initialise_called) else $fatal(0, "Must call initialise on tx_interface_source");
    end

    // sends out a frame
    task send_frame (logic [iface.DATA_WIDTH-1:0] sq[$], int bits_in_first_byte = 0, int timeout=0);
        automatic int bits_left_in_byte;

        if (!iface.BY_BYTE) begin
            // when we are sending bits, the bits in the first byte has to be
            // set so that the entire transfer ends with a full byte
            bits_in_first_byte = sq.size % 8;
        end
        bits_left_in_byte = (bits_in_first_byte == 0) ? 8 : bits_in_first_byte;

        // set bits for first byte (only relevant if iface.BY_BYTE == 1)
        iface.data_bits <= 3'(bits_in_first_byte);

        fork
            // process 1 - timeout
            begin
                if (timeout != 0) begin
                    repeat (timeout) @(posedge clk) begin end
                    $error("tx_interface_source.send_frame timed out after %d ticks", timeout);
                end
                else begin
                    forever begin end
                end
            end

            // process 2 - send the data
            begin
                foreach (sq[i]) begin
                    bits_left_in_byte--;

                    // set up the inputs
                    iface.data              <= sq[i];
                    iface.data_valid        <= 1'b1;
                    iface.last_bit_in_byte  <= (bits_left_in_byte == 0);    // only relevant for iface.BY_BYTE == 0

                    // wait a tick so req isn't asserted still
                    @(posedge clk)

                    // wait for the next req, and align to the clock
                    wait (iface.req) begin end
                    @(posedge clk) begin end

                    // all remaining bytes have 8 bits per byte (only relevant for iface.BY_BYTE == 1)
                    iface.data_bits <= 3'd0;

                    if (bits_left_in_byte == 0) begin
                        bits_left_in_byte = 8;
                    end
                end
            end
        join_any

        // disable the remaining process
        disable fork;

        // nothing more to send
        iface.data_valid <= 1'b0;

        if (!iface.BY_BYTE) begin: byBit
            // confirm last_bit_in_byte is asserted
            // this is to sanity check my implementation
            checkLastBitInByte:
                assert (iface.last_bit_in_byte) else $error("finished sending and last_bit_in_byte is not asserted");
        end
    endtask

endmodule
