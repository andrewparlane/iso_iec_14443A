/***********************************************************************
        File: tx.sv
 Description: Code to transmit data to the PCD
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

// The sender sets data, data_bits and ready_to_send as soon as it is ready.
// when the fdt_trigger fires if ready_to_send is set, we start sending out data_bits bits
// plus a parity bit (There is no occasion when we don't want to transmit the parity bit).
// Oncne we've started sending we assert req for one tick. The sender should then update
// the data, data_bits and ready_to_send signals. If it has nothing more to send it can deassert
// ready_to_send. We continue transmitting bits until we finish the current byte (or partial byte)
// and ready_to_send is deasserted.

module tx
(
    // clk is our 13.56MHz input clock.
    input                   clk,

    // rst is our active low synchronised asynchronous reset signal
    input                   rst_n,

    // input from the frame delay timer
    // this triggers the send (if ready_to_send is set)
    input                   fdt_trigger,

    // information about the data to send
    input           [7:0]   data,
    input           [2:0]   data_bits,      // 0 -> send 8 bits
    input                   ready_to_send,  // there is data to send

    // request for more data
    output logic            req,

    // the Tx output signal is the manchester encoded data AND'ed with the subcarrier
    output logic            tx
);

    enum
    {
        State_IDLE,
        State_SOC,
        State_DATA,
        State_PARITY,
        State_EOC
    } state;

    // state vars
    logic [7:0] data_cached;
    logic [2:0] bits_remaining;
    logic       parity;

    // signals from the bit_encoder
    logic       be_req;         // requesting the next bit
    logic       be_last_tick;   // the last tick of the bit period

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            state <= State_IDLE;
            req <= 1'b0;
        end
        else begin
            // req should only ever be asserted one tick at a time
            req <= 1'b0;

            case (state)
                State_IDLE: begin
                    // we're idle
                    // wait for fdt_trigger
                    if (fdt_trigger) begin
                        // start if ready_to_send
                        if (ready_to_send) begin
                            // send the SOC
                            state <= State_SOC;

                            // cache the current data
                            bits_remaining  <= data_bits;
                            data_cached     <= data;
                        end
                    end
                end

                State_SOC: begin
                    // when the REQ comes in from the bit encoder then switch to the data state
                    if (be_req) begin
                        state           <= State_DATA;
                        // since data_bits == 0 implies sending 8 bits
                        // we decrement here, which will underflow to 7
                        // so we don't hit the == 0 in State_DATA
                        bits_remaining  <= bits_remaining - 1'd1;

                        parity <= 1'b1;
                    end
                end

                State_DATA: begin
                    // when the REQ comes in from the bit encoder shift the data right by one
                    // ignoring the MSb. Or go to the parity stage
                    if (be_req) begin
                        // currently sending data_cached[0]
                        // update the parity bit
                        parity <= parity ^ data_cached[0];

                        if (bits_remaining == 0) begin
                            state               <= State_PARITY;

                            // nothing left for us to send, request more
                            req                 <= 1'b1;
                        end
                        else begin
                            data_cached[6:0]    <= data_cached[7:1];
                            bits_remaining      <= bits_remaining - 1'd1;
                        end
                    end
                end

                State_PARITY: begin
                    // wait for the bit encoder to request more data
                    if (be_req) begin
                        // is there new data?
                        if (ready_to_send) begin
                            // cache the new data
                            data_cached     <= data;
                            bits_remaining  <= data_bits - 1'd1;

                            // go to the data state
                            state           <= State_DATA;
                            parity          <= 1'b1;
                        end
                        else begin
                            // nothing else to send
                            // wait for last_tick and then go idle
                            state           <= State_EOC;
                        end
                    end
                end

                State_EOC: begin
                    // just wait for us to be at the end of the bit time and then disable
                    // the subcarrier and bit_encoder
                    if (be_last_tick) begin
                        state <= State_IDLE;
                    end
                end

                default: begin
                    state <= State_IDLE;
                end
            endcase
        end
    end

    // enable the subcarrier and the bit_encoder
    logic en;
    assign en = (state != State_IDLE);

    // The bit to send is either the SOC (logic 1)  see ISE/IEC 14443-2:2016 section 8.2.5.1
    // the next bit of data (LSb first)             see ISE/IEC 14443-3:2016 section 6.2.3.1
    // or the parity bit                            see ISE/IEC 14443-3:2016 section 6.2.3.1
    logic bit_to_send;
    always_comb begin
        case (state)
            State_SOC:      bit_to_send = 1'b1;
            State_DATA:     bit_to_send = data_cached[0];
            State_PARITY:   bit_to_send = parity;

            //State_IDLE:
            //State_EOC:
            default:        bit_to_send = 1'b0;
        endcase
    end

    // generate our subcarrier signal
    logic subcarrier;
    subcarrier sc_inst
    (
        .clk        (clk),
        .rst_n      (rst_n),
        .en         (en),
        .subcarrier (subcarrier)
    );

    // convert the bit to manchester encoding over 128 ticks
    logic encoded_data;
    bit_encoder bc_inst
    (
        .clk            (clk),
        .rst_n          (rst_n),
        .data           (bit_to_send),
        .en             (en),
        .encoded_data   (encoded_data),
        .req            (be_req),
        .last_tick      (be_last_tick)
    );

    // the data we actually send is the AND of the subcarrier with the manchester encoded data
    assign tx = subcarrier & encoded_data;

endmodule
