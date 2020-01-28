/***********************************************************************
        File: frame_decode.sv
 Description: Turns PCDBitSequences into SOC, EOC, and data bytes
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

import ISO14443A_pkg::*;

module frame_decode
(
    // clk is our 13.56MHz input clock. It is recovered from the carrier wave,
    // and as such stops during pause frames. It must not have any glitches.
    input                       clk,

    // rst is our active low synchronised asynchronous reset signal
    input                       rst_n,

    // inputs from sequence_decode
    input PCDBitSequence        sd_seq,
    input                       sd_seq_valid,

    // outputs
    output logic                soc,                // start of comms
    output logic                eoc,                // end of comms
    output logic [7:0]          data,
    output logic [2:0]          data_bits,          // number of valid data bits in data. 0 means all 8 bits are present
    output logic                data_valid,
    output logic                sequence_error,
    output logic                parity_error
);

    logic           idle;               // are we currently idle
    PCDBitSequence  last_seq;           // last sequence received (so we can detect EOC)
    logic           next_bit;           // decode the sequence to a bit
    logic           data_received;      // have we received anything yet? Used to prevent 0 bit frames
    logic           next_bit_is_parity; // after every 8 bits of data we expect a parity bit
    logic           expected_parity;    // what should the parity bit be
    logic           error_detecetd;     // don't issue data after we detect an error

    // Note: we use last_seq everywhere instead of sd_seq because
    //       the EOC is logical '0' followed by Y. If we look at
    //       sd_seq then we see and interpret that logical '0' as a 0
    //       and only detect EOC on the next sd_seq_valid.

    // small bit of combinatory logic to determine what the next bit will be
    // this is only true when sd_seq_valid is asserted.
    // and it does not detect EOC or errors.
    assign next_bit = (last_seq == PCDBitSequence_X);

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            soc                 <= 0;
            eoc                 <= 0;
            data_valid          <= 0;
            parity_error        <= 0;
            sequence_error      <= 0;

            next_bit_is_parity  <= 0;
            idle                <= 1;
            last_seq            <= PCDBitSequence_Y; // idle
        end
        else begin
            // these should only be asserted for one tick
            soc             <= 0;
            eoc             <= 0;
            data_valid      <= 0;
            parity_error    <= 0;
            sequence_error  <= 0;

            // nothing to do if !sd_seq_valid
            if (sd_seq_valid) begin
                last_seq <= sd_seq;

                if (idle) begin
                    // wait for PCDBitSequence_Z
                    // we could get a PCDBitSequence_Y here
                    // but that's just the idle state at the end of the last frame
                    // so we ignore it.

                    if (last_seq == PCDBitSequence_Z) begin
                        // This is the start of comms
                        soc                 <= 1;
                        data_bits           <= 0;
                        idle                <= 0;
                        expected_parity     <= 1;
                        next_bit_is_parity  <= 0;
                        data_received       <= 0;
                        error_detecetd      <= 0;
                    end
                end
                else begin

                    // Check for EOC
                    if ((sd_seq == PCDBitSequence_Y) &&
                        ((last_seq == PCDBitSequence_Y) || (last_seq == PCDBitSequence_Z))) begin
                        eoc     <= 1;
                        idle    <= 1;

                        if (next_bit_is_parity) begin
                            // this is an error
                            // if you have 8 data bits you must have a parity bit
                            parity_error <= 1;
                        end

                        if (!data_received) begin
                            // 0 byte frame, consists of sequences ZY
                            // this is a sequence error
                            sequence_error <= 1;
                        end

                        if (!next_bit_is_parity && data_received && !error_detecetd) begin
                            // could be a broken byte frame, need to assert
                            // data_valid if data_bits != 0
                            data_valid <= data_bits != 0;
                        end
                    end
                    // if we've detected an error don't do anything just wait for EOC
                    else if (!error_detecetd) begin
                        // we've at least received one bit of data
                        // even if it's a sequence error
                        data_received <= 1;

                        // Check for error
                        if (last_seq == PCDBitSequence_ERROR) begin
                            sequence_error      <= 1;
                            error_detecetd      <= 1;
                            // clear this so we don't report parity error in EOC
                            next_bit_is_parity  <= 0;
                        end
                        // Is it the parity bit?
                        else if (next_bit_is_parity) begin
                            next_bit_is_parity <= 0;

                            // next_bit is the received parity_bit
                            // check it's correct
                            if (expected_parity == next_bit) begin
                                // all good
                                data_bits   <= 0; // represents 8 valid data bits, also ready for next byte
                                data_valid  <= 1;
                                expected_parity <= 1;
                            end
                            else begin
                                // parity error
                                parity_error    <= 1;
                                error_detecetd  <= 1;
                            end
                        end
                        // otherwise it's just a data bit
                        else begin
                            data_received   <= 1;
                            data[data_bits] <= next_bit;

                            if (next_bit) begin
                                // we got a 1 so flip the expected_parity bit
                                expected_parity <= !expected_parity;
                            end

                            if (data_bits == 3'd7) begin
                                // last data bit received
                                next_bit_is_parity <= 1;
                            end

                            data_bits <= data_bits + 1'd1;
                            // TODO: is data[data_bits] allowed?
                            //       is it optimal?
                            //       I could do data[7] <= next_bit; and then shift it
                            //       but if there's less than 8 bits we wouldn't end up with
                            //       data aligned correctly. We could maybe run some extra
                            //       shifting cycles after EOC before we report everything?
                        end
                    end
                end
            end
        end
    end

endmodule
