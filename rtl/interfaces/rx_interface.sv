/***********************************************************************
        File: rx_interface.sv
 Description: An interface for the Rx path
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

interface rx_interface
#(
    // are we a bit by bit interface (ie before the deserialiser) or a byte by byte interface (ie. after).
    // When we are by byte we use the data_bits signal to indicate partial bytes
    parameter logic BY_BYTE     = 0,
    parameter logic USE_ASSERTS = 1
)
(
    input clk,
    input rst_n
);

    localparam DATA_WIDTH = BY_BYTE ? 8 : 1;

    logic                   soc;
    logic                   eoc;
    logic [DATA_WIDTH-1:0]  data;
    logic                   data_valid;
    logic [2:0]             data_bits;  // 0 -> 8 bits, only used if BY_BYTE==1
    logic                   error;

    modport in_bit
    (
        input soc,
        input eoc,
        input data,
        input data_valid,
        input error
    );

    modport in_byte
    (
        input soc,
        input eoc,
        input data,
        input data_valid,
        input data_bits,
        input error
    );

    modport out_bit
    (
        output soc,
        output eoc,
        output data,
        output data_valid,
        output error
    );

    modport out_byte
    (
        output soc,
        output eoc,
        output data,
        output data_valid,
        output data_bits,
        output error
    );

    // ------------------------------------------------------------------------
    // Verification
    // ------------------------------------------------------------------------
    // only for use in testbenches

`ifndef SYNTHESIS

    function string to_string;
        string s;
        s = $sformatf("{soc: %b, eoc: %b, data_valid: %b, data_bits: %d, data: %x, error: %b}",
                      soc, eoc, data_valid, data_bits, data, error);
        return s;
    endfunction

    generate
        if (USE_ASSERTS) begin: useAsserts
            function logic validate;
                automatic logic err = 1'b0;

                //$display("validating");

                // soc, eoc, error, data_valid can never be unknown
                if ($isunknown(soc)     ||
                    $isunknown(eoc)     ||
                    $isunknown(error)   ||
                    $isunknown(data_valid)) begin
                    err = 1'b1;
                    //$display("not valid because of unknown");
                end

                if (soc) begin
                    // no other flags can be set
                    if (eoc || error || data_valid) begin
                        err = 1'b1;
                        //$display("not valid because of soc + other");
                    end
                end

                if (eoc) begin
                    // soc can't be set
                    if (soc) begin
                        err = 1'b1;
                        //$display("not valid because of eoc + soc");
                    end
                    // data_valid can only be set if BY_BYTE and data_bits != 0
                    if (data_valid && (!BY_BYTE || (data_bits == 0))) begin
                        err = 1'b1;
                        //$display("not valid because of eoc + data_valid");
                    end
                end

                if (error) begin
                    // only eoc can be set
                    if (soc || data_valid) begin
                        err = 1'b1;
                        //$display("not valid because of error + something");
                    end
                end

                if (data_valid) begin
                    // soc and error can't be set
                    if (soc || error) begin
                        err = 1'b1;
                        //$display("not valid because of data_valid + something");
                    end

                    // eoc can only be set if BY_BYTE and bit_count != 0
                    if (eoc && (!BY_BYTE || (data_bits == 0))) begin
                        err = 1'b1;
                        //$display("not valid because of data_valid + eoc");
                    end
                end

                //$display("result: %b", err);

                return !err;
            endfunction

            // TODO: check outputs_valid and validate are optimised out in synthesis

            // have to put this in an initial block, because I can't call validate() from the assertion
            // since VCS complains about none constant functions in assertions (even though it is constant)
            // and using a temp variable only assigns to it once at startup, meaning everything is unknown
            initial begin: rxInterfaceInitial
                automatic logic outputs_valid;
                forever begin: foreverBlock

                    @(posedge clk)
                    outputs_valid = validate();

                    outputsValid:
                    assert (outputs_valid)
                        else $error("Current outputs not valid. soc %b, eoc %b, error %b, valid %b, data %X, data_bits %d",
                                    soc, eoc, error, data_valid, data, data_bits);
                end
            end

            // Check that the outputs are correct when in reset
            signalsInReset:
            assert property (
                @(posedge clk)
                !rst_n |->
                    (!soc && !eoc && !error && !data_valid))
                else $error("Outputs not as expected whilst in reset");

            // soc is only valid for one tick at a time
            socOnlyOneTick:
            assert property (
                @(posedge clk)
                soc |=> !soc)
                else $error("soc asserted for more than one tick");

            // eoc is only valid for one tick at a time
            eocOnlyOneTick:
            assert property (
                @(posedge clk)
                eoc |=> !eoc)
                else $error("eoc asserted for more than one tick");

            // error is only valid for one tick at a time
            errorOnlyOneTick:
            assert property (
                @(posedge clk)
                error |=> !error)
                else $error("error asserted for more than one tick");

            // data_valid is only valid for one tick at a time
            dataValidOnlyOneTick:
            assert property (
                @(posedge clk)
                data_valid |=> !data_valid)
                else $error("data_valid asserted for more than one tick");
        end
    endgenerate

`endif  // SYNTHESIS

endinterface
