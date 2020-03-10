/***********************************************************************
        File: rx_interface_source.sv
 Description: Source for the rx_interface
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

module rx_interface_source
(
    input                   clk,
    rx_interface.out_byte   iface
);

    function void initialise;
        iface.soc           <= 1'b0;
        iface.eoc           <= 1'b0;
        iface.data_valid    <= 1'b0;
        iface.error         <= 1'b0;
    endfunction

    // sends out a frame, with an optional error
    task send_frame (logic [iface.DATA_WIDTH-1:0] sq[$], int bits_in_last_byte=0, int error_before_bit=-1);
        automatic logic                         errorSent = 1'b0;
        automatic logic [iface.DATA_WIDTH-1:0]  last_byte;

        // bits_in_last_byte == 0 and == 8 are sort of the same thing
        // we allow both to be used here
        if (bits_in_last_byte == 8) begin
            bits_in_last_byte = 0;
        end

        if (iface.BY_BYTE && (bits_in_last_byte != 0)) begin
            // pop off the last value of sq
            last_byte = sq.pop_back;
        end

        // sync to a clock edge
        @(posedge clk) begin end

        // default to sending full bytes (ignored if !BY_BYTE)
        iface.data_bits <= 0;

        // SOC
        iface.soc <= 1'd1;
        @(posedge clk)
        iface.soc <= 1'd0;

        // data
        foreach (sq[i]) begin
            repeat (5) @(posedge clk) begin end // sync to clock edge and delay between bits

            // error?
            if (error_before_bit == i) begin
                iface.error     <= 1'b1;
                @(posedge clk)
                iface.error     <= 1'b0;
                repeat (5) @(posedge clk) begin end

                errorSent = 1'b1;
            end

            iface.data          <= sq[i];
            iface.data_valid    <= 1'b1;
            @(posedge clk)
            iface.data_valid    <= 1'b0;
        end

        repeat (5) @(posedge clk) begin end

        // error?
        if ((error_before_bit != -1) && !errorSent) begin
            // send the error on the EOC
            iface.error         <= 1'b1;
        end
        else if (iface.BY_BYTE && (bits_in_last_byte != 0)) begin
            // partial byte
            iface.data_bits     <= 3'(bits_in_last_byte);
            iface.data_valid    <= 1'b1;
            iface.data          <= last_byte;
        end

        // eoc
        iface.eoc           <= 1'b1;
        @(posedge clk)
        iface.eoc           <= 1'b0;
        iface.error         <= 1'b0;
        iface.data_valid    <= 1'b0;

    endtask

endmodule
