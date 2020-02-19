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

// The user sets data and asserts send
// when req asserts if there is more bits to send then
// the data should be updated and send should remain asserted
// If there's no more data to send then send should be deasserted

module tx
(
    // clk is our 13.56MHz input clock.
    input                   clk,

    // rst is our active low synchronised asynchronous reset signal
    input                   rst_n,

    // information about the data to send
    input                   data,
    input                   send,

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
        State_EOC
    } state;

    // state vars
    logic       data_cached;

    // signals from the bit_encoder
    logic       be_req;         // requesting the next bit
    logic       be_last_tick;   // the last tick of the bit period

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            state   <= State_IDLE;
            req     <= 1'b0;
        end
        else begin
            // req should only ever be asserted one tick at a time
            req     <= 1'b0;

            case (state)
                State_IDLE: begin
                    // we're idle
                    // wait for a send request
                    if (send) begin
                        // send the SOC
                        state       <= State_SOC;

                        // cache the current data
                        data_cached <= data;
                    end
                end

                State_SOC: begin
                    // when the REQ comes in from the bit encoder then switch to the data state
                    // and request more data
                    if (be_req) begin
                        state           <= State_DATA;
                        req             <= 1'b1;
                    end
                end

                State_DATA: begin
                    // when the REQ comes in if we still have more to send then cache the new data
                    // and request more. Otherwise go to EOC
                    if (be_req) begin
                        if (send) begin
                            data_cached <= data;
                            req         <= 1'b1;
                        end
                        else begin
                            state       <= State_EOC;
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

    // The bit to send is either the SOC (logic 1, see ISE/IEC 14443-2:2016 section 8.2.5.1)
    // or the data
    logic bit_to_send;
    assign bit_to_send = (state == State_SOC) ? 1'b1 : data_cached;

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
