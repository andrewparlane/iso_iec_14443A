/***********************************************************************
        File: crc_a_tb
 Description: Testbench for crc_a
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

module crc_a_tb;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic           clk;
    logic           rst_n;

    logic           start;
    logic           data;
    logic           sample;
    logic [15:0]    crc;

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    crc_a dut (.*);

    // --------------------------------------------------------------
    // Clock generator
    // --------------------------------------------------------------

    clock_source clock_source_inst (.*);

    typedef rx_byte_transaction_pkg::RxByteTransaction  ByteTransType;
    typedef rx_bit_transaction_pkg::RxBitTransaction    BitTransType;

    // --------------------------------------------------------------
    // Functions / Tasks
    // --------------------------------------------------------------

    // I know of two ways to generate the CRC:
    //  1) using the algorithm in ByteQueueTransaction::calculate_crc()
    //     which is based on the C code in ISO/IEC 14443-3:2016 Annex B.3
    //  2) using an LFSR with polynomial: x^16 + x^12 + x^5 + 1
    // I test the result of crc_a against both of these

    function logic [15:0] calculate_crc_lfsr (ref BitTransType trans);
        // note 0:15 not 15:0
        automatic logic [0:15] lfsr = 16'h6363;

        //$display("calculate_crc_lfsr %p", bq);

        foreach (trans.data[i]) begin
            //$display("  parsing bit %d (%b)", i, trans.data[i]);

            // do this first so we don't overwrite lfsr[15] before we use it
            automatic logic tmp = trans.data[i] ^ lfsr[15];

            // shift each bit (except for 12, 5, 0)
            // normal bits are: lfsr[idx] <= lfsr[idx-1];
            // special bits are lfsr[idx] <= lfsr[idx-1] ^ tmp;
            // except for idx=0: lfsr[0] <= tmp;
            for (int idx = 15; idx > 0; idx--) begin
                if ((idx ==  12) || (idx == 5)) begin
                    lfsr[idx] = lfsr[idx - 1] ^ tmp;
                end
                else begin
                    lfsr[idx] = lfsr[idx-1];
                end
            end
            lfsr[0] = tmp;
        end

        return lfsr;
    endfunction

    task testCRC (ByteTransType trans, output logic [15:0] crc_a_res);
        automatic BitTransType bit_trans = new(trans.convert_to_bit_queue);
        automatic logic [15:0] lfsr_res;
        automatic logic [15:0] trans_res;

        //$display("testCRC %p", trans.dq);

        // get the result from the method in the transaction class
        trans_res   = trans.calculate_crc;
        //$display("trans_res: %h", trans_res);

        // get the result from the LFSR method
        lfsr_res    = calculate_crc_lfsr(bit_trans);
        //$display("lfsr_res: %h", lfsr_res);

        // get the result from the DUT
        @(posedge clk) begin end

        // TODO: if we cared we could make this into a driver.
        //       either reusing the rx_bit_iface_driver,
        //          sample = data_valid
        //          start = SOC
        //          ignore other signals
        //       or a custom driver
        //       However since this is the only tb that interacts with the crc_a module
        //       there's not much point
        start       <= 1'b1;
        sample      <= 1'b0;
        @(posedge clk) begin end
        start       <= 1'b0;
        @(posedge clk) begin end

        foreach (bit_trans.data[i]) begin
            data        <= bit_trans.data[i];
            sample      <= 1'b1;
            @(posedge clk) begin end
            sample      <= 1'b0;
            @(posedge clk) begin end
        end

        crc_a_res   = crc;
        //$display("crc_a res %h", crc_a_res);

        // validate
        fgpEqualLfsr:
        assert (trans_res == lfsr_res) else $error("calculate_crc() = (%h) != lfsr_res (%h)", trans_res, lfsr_res);

        crcAValid:
        assert (trans_res == crc_a_res) else $error("calculate_crc() = (%h) != crc_a_res (%h)", trans_res, crc_a_res);
    endtask

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin: testStimulus
        automatic ByteTransType trans       = new;
        automatic logic [15:0]  crc_a_res;

        start       <= 1'b0;
        sample      <= 1'b0;

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // Test no data (should be 16'h6363)
        trans.data = '{};
        testCRC(trans, crc_a_res);
        emptyData:
        assert (crc_a_res == 16'h6363) else $error("Empty data produces CRC %h", crc_a_res);

        // Test '{8'h0,8'h0}, given as an example in ISO/IEC 14443-3:2016 Annex B
        trans.data = '{8'h0, 8'h0};
        testCRC(trans, crc_a_res);
        exTwoZeros:
        assert (crc_a_res == 16'h1EA0) else $error("'{0,0} produces CRC %h", crc_a_res);

        // Test '{8'h12,8'h34}, given as an example in ISO/IEC 14443-3:2016 Annex B
        trans.data = '{8'h12, 8'h34};
        testCRC(trans, crc_a_res);
        ex1234:
        assert (crc_a_res == 16'hCF26) else $error("'{8'h12,8'h34} produces CRC %h", crc_a_res);

        // random tests
        repeat (1000) begin: randomTests
            trans = ByteTransType::new_random_transaction($urandom_range(0, 10), 0);

            // just test the generated data
            testCRC(trans, crc_a_res);

            // append the CRC LSByte first to the generatedData and check again
            // result should be 0
            trans.append_crc;
            testCRC(trans, crc_a_res);

            crcIsZero:
            assert(crc_a_res == 0) else $error("data with crc appended should produce CRC 0 not %h", crc_a_res);
        end

        // assert reset for toggle coverage
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        $stop;
    end


    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

endmodule
