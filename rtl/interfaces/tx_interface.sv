/***********************************************************************
        File: tx_interface.sv
 Description: An interface for the Tx path
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

interface tx_interface
#(
    // are we a bit by bit interface (ie after the serialiser) or a byte by byte interface (ie. before).
    // When we are by byte we use the data_bits signal to indicate partial bytes
    parameter logic BY_BYTE     = 0,
    parameter logic USE_ASSERTS = 1
)
(
    input clk,
    input rst_n
);

    localparam DATA_WIDTH = BY_BYTE ? 8 : 1;

    // When transmitting the source sets data, data_valid and data_bits (if applicable)
    // and waits. The sink reads data when it wants it and then asserts req for one tick
    // indicating that the source should update it's outputs. If the source has nothing more
    // to send then it should deassert data_valid.
    // This is not ideal, as there is no indication as to how long the source has to update
    // data, however we use bit times of 128 ticks, in bit_encoder.sv we set req on count 64
    // and use the new data when the count overflows to 0. So we have 64 ticks to get the data
    // ready. I recommend taking no more than 4 ticks. As such I have an assert that
    // data / data_bits / data_valid can't change more than 4 ticks after req asserts
    // (except for when we are starting new sends (data_valid is low))

    logic [DATA_WIDTH-1:0]  data;
    logic                   data_valid;
    logic [2:0]             data_bits;          // 0 -> 8 bits, only used if BY_BYTE==1
    logic                   last_bit_in_byte;   // only used if BY_BYTE==0
    logic                   req;

    modport in_bit
    (
        input   data,
        input   data_valid,
        input   last_bit_in_byte,
        output  req
    );

    // the crc_control just sniffs the bus, it does not drive any signal
    modport monitor_bit
    (
        input   data,
        input   data_valid,
        input   last_bit_in_byte,
        input   req
    );

    modport in_byte
    (
        input   data,
        input   data_valid,
        input   data_bits,
        output  req
    );

    modport out_bit
    (
        output  data,
        output  data_valid,
        output  last_bit_in_byte,
        input   req
    );

    modport out_byte
    (
        output  data,
        output  data_valid,
        output  data_bits,
        input   req
    );

    // ------------------------------------------------------------------------
    // Verification
    // ------------------------------------------------------------------------
    // only for use in testbenches

`ifndef SYNTHESIS

    // for use with the bfms
    modport in_all
    (
        input   data,
        input   data_valid,
        input   data_bits,
        input   last_bit_in_byte,
        output  req
    );

    modport out_all
    (
        output  data,
        output  data_valid,
        output  data_bits,
        output  last_bit_in_byte,
        input   req
    );

    generate
        if (USE_ASSERTS) begin: useAsserts

            // Check that the signals are correct when in reset
            signalsInReset:
            assert property (
                @(posedge clk)
                !rst_n |->
                    (!req && !data_valid))
                else $error("Signals not as expected whilst in reset");

            // req is only asserted for one tick at a time
            reqOnlyOneTick:
            assert property (
                @(posedge clk)
                req |=> !req)
                else $error("req asserted for more than one tick");

            // data, data_valid, data_bits and last_bit_in_byte can only change either when data_valid is low
            // or within 4 ticks of req asserting.
            signalChangesOnlyAfterReqOrWhenIdle:
            assert property (
                @(posedge clk)
                (!$stable(data)         || !$stable(data_valid) ||
                 !$stable(data_bits)    || !$stable(last_bit_in_byte)) |->
                    ($rose(data_valid)                  ||  // we were not valid before (so idle)
                     (data_valid == 0)                  ||  // we are no longer valid
                     $past(req, 1) || $past(req, 2)     ||  // or req asserted one of the previous 4 ticks
                     $past(req, 3) || $past(req, 4)))
                else $error("data, data_valid or data_bits changed when not idle and not immediately after req");
        end
    endgenerate

`endif  // SYNTHESIS

endinterface
