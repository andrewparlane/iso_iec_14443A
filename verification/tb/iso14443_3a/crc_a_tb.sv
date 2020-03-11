/***********************************************************************
        File: crc_a_tb
 Description: Testbench for crc_a
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

    // Calculate our clock period in ps
    localparam CLOCK_FREQ_HZ = 13560000; // 13.56MHz
    localparam CLOCK_PERIOD_PS = 1000000000000.0 / CLOCK_FREQ_HZ;
    initial begin
        clk = 1'b0;
        forever begin
            #(int'(CLOCK_PERIOD_PS/2))
            clk = ~clk;
        end
    end

    // --------------------------------------------------------------
    // Functions / Tasks
    // --------------------------------------------------------------

    // I know of two ways to generate the CRC:
    //  1) using the algorithm in frame_generator_pkg::calculate_crc()
    //     which is based on the C code in ISO/IEC 14443-3:2016 Annex B.3
    //  2) using an LFSR with polynomial: x^16 + x^12 + x^5 + 1
    // I test the result of crc_a against both of these

    function logic [15:0] calculate_crc_lfsr (logic bq[$]);
        // note 0:15 not 15:0
        automatic logic [0:15] lfsr = 16'h6363;

        //$display("calculate_crc_lfsr %p", bq);

        foreach (bq[i]) begin
            //$display("  parsing bit %d (%b)", i, bq[i]);

            // do this first so we don't overwrite lfsr[15] before we use it
            automatic logic tmp = bq[i] ^ lfsr[15];

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

    task testCRC (input logic [7:0] dq[$], output logic [15:0] crc_a_res);
        automatic logic [15:0] lfsr_res;
        automatic logic [15:0] fgp_res;

        //$display("testCRC %p", dq);

        // get the result from the method in the frame_generator_pkg
        fgp_res     = frame_generator_pkg::calculate_crc(dq);
        //$display("fgp_res: %h", fgp_res);

        // get the result from the LFSR method
        lfsr_res    = calculate_crc_lfsr(frame_generator_pkg::convert_message_to_bit_queue(dq, 8));
        //$display("lfsr_res: %h", lfsr_res);

        // get the result from the DUT
        @(posedge clk) begin end

        start       <= 1'b1;
        sample      <= 1'b0;
        @(posedge clk) begin end
        start       <= 1'b0;
        @(posedge clk) begin end

        foreach (dq[i]) begin
            automatic logic [7:0] d = dq[i];
            for (int j = 0; j < 8; j++) begin // LSb first
                //$display("passing byte %d, bit %d (%h)", i, j, dq[i][j]);
                data        <= d[j];
                sample      <= 1'b1;
                @(posedge clk) begin end
                sample      <= 1'b0;
                @(posedge clk) begin end
            end
        end

        crc_a_res   = crc;
        //$display("crc_a res %h", crc_a_res);

        // validate
        fgpEqualLfsr:
        assert (fgp_res == lfsr_res) else $error("FGP result (%h) != lfsr_res (%h)", fgp_res, lfsr_res);

        crcAValid:
        assert (fgp_res == crc_a_res) else $error("FGP result (%h) != crc_a_res (%h)", fgp_res, crc_a_res);
    endtask

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin: testStimulus
        automatic logic [7:0]   generatedData [$];
        automatic logic [15:0]  crc_a_res;

        start       <= 1'b0;
        sample      <= 1'b0;

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // Test no data (should be 16'h6363)
        generatedData = '{};
        testCRC(generatedData, crc_a_res);
        emptyData:
        assert (crc_a_res == 16'h6363) else $error("Empty data produces CRC %h", crc_a_res);

        // Test '{8'h0,8'h0}, given as an example in ISO/IEC 14443-3:2016 Annex B
        generatedData = '{8'h0, 8'h0};
        testCRC(generatedData, crc_a_res);
        exTwoZeros:
        assert (crc_a_res == 16'h1EA0) else $error("'{0,0} produces CRC %h", crc_a_res);

        // Test '{8'h12,8'h34}, given as an example in ISO/IEC 14443-3:2016 Annex B
        generatedData = '{8'h12, 8'h34};
        testCRC(generatedData, crc_a_res);
        ex1234:
        assert (crc_a_res == 16'hCF26) else $error("'{8'h12,8'h34} produces CRC %h", crc_a_res);

        // random tests
        repeat (1000) begin: randomTests
            automatic int bytes = $urandom_range(1, 100);

            // just test the generated data
            generatedData = frame_generator_pkg::generate_byte_queue(bytes);
            testCRC(generatedData, crc_a_res);

            // append the CRC LSByte first to the generatedData and check again
            // result should be 0
            generatedData.push_back(crc_a_res[7:0]);
            generatedData.push_back(crc_a_res[15:8]);
            testCRC(generatedData, crc_a_res);

            crcIsZero:
            assert(crc_a_res == 0) else $error("data with crc appended should produce CRC 0 not %h", crc_a_res);
        end

        repeat (5) @(posedge clk) begin end
        $stop;
    end


    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

endmodule
