/***********************************************************************
        File: tx.sv
 Description: Code to transmit data to the PCD
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

// The user sets data and asserts valid
// when req asserts if there is more bits to send then
// the data should be updated and valid should remain asserted
// If there's no more data to send then valid should be deasserted

module tx
(
    // clk is our 13.56MHz input clock.
    input                   clk,

    // rst is our active low synchronised asynchronous reset signal
    input                   rst_n,

    // data to send
    tx_interface.in_bit     in_iface,

    // the lm_out signal is the manchester encoded data AND'ed with the subcarrier
    // which is sent to the load modulator
    output logic            lm_out
);

    enum
    {
        State_IDLE,
        State_SOC,
        State_DATA,
        State_EOC
    } state;

    // signals from the bit_encoder
    logic       be_last_tick;   // the last tick of the bit period

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            state           <= State_IDLE;
            in_iface.req    <= 1'b0;
        end
        else begin
            // req should only ever be asserted one tick at a time
            in_iface.req    <= 1'b0;

            case (state)
                State_IDLE: begin
                    // we're idle
                    // wait for data to go valid
                    if (in_iface.data_valid) begin
                        // send the SOC
                        state       <= State_SOC;
                    end
                end

                State_SOC: begin
                    // when the REQ comes in from the bit encoder then switch to the data state
                    // which starts sending the first bit of data
                    if (be_iface.req) begin
                        state           <= State_DATA;
                    end
                end

                State_DATA: begin
                    // when the REQ comes in if we still have more to send (data is valid)
                    // then cache the new data and request more. Otherwise go to EOC
                    if (be_iface.req) begin
                        if (in_iface.data_valid) begin
                            in_iface.req    <= 1'b1;
                        end
                    end
                    else if (be_last_tick && !in_iface.data_valid) begin
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
    assign bit_to_send = (state == State_SOC) ? 1'b1 : in_iface.data;

    // generate our subcarrier signal
    logic subcarrier;
    subcarrier sc_inst
    (
        .clk        (clk),
        .rst_n      (rst_n),
        .en         (en),
        .subcarrier (subcarrier)
    );

    tx_interface #(.BY_BYTE(0)) be_iface (.*);
    assign be_iface.data                = bit_to_send;
    assign be_iface.data_valid          = in_iface.data_valid && (state != State_IDLE);
    assign be_iface.last_bit_in_byte    = in_iface.last_bit_in_byte;
    // TODO: Check data_valid and last_bit_in_byte are optimised out
    // check last_bit_in_byte is optimised out all the way up the chain
    // it's only used in serialiser -> frame_encode

    // convert the bit to manchester encoding over 128 ticks
    logic encoded_data;
    bit_encoder bc_inst
    (
        .clk            (clk),
        .rst_n          (rst_n),
        .en             (en),
        .in_iface       (be_iface),
        .encoded_data   (encoded_data),
        .last_tick      (be_last_tick)
    );

    // the data we actually send is the AND of the subcarrier with the manchester encoded data
    // We register the output to prevent glitches reaching the load modulator
    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            lm_out <= 1'b0;
        end
        else begin
            lm_out <= subcarrier & encoded_data;
        end
    end

endmodule
