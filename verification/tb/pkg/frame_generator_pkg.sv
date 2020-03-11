/***********************************************************************
        File: frame_generator_pkg.sv
 Description: Generates PCD -> PICC and PICC -> PCD frames
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

package frame_generator_pkg;

    import ISO14443A_pkg::*;

    // ------------------------------------------------------------------------
    // Helper types (so we can return arrays from functions
    // ------------------------------------------------------------------------
    typedef PCDBitSequence  PCDBitSequenceQueue [$];
    typedef logic           bit_queue           [$];
    typedef logic [7:0]     byte_queue          [$];

    // ------------------------------------------------------------------------
    // internal functions
    // ------------------------------------------------------------------------

    // use the convert_message_to_bit_queue_for_rx / _for_tx functions instead
    function bit_queue convert_message_to_bit_queue_internal (logic [7:0] data [$], int bits_in_first_byte=8, int bits_in_last_byte=8);
        // build a bit queue
        bit_queue bits;
        int last_byte;

        // in some places we use 0 to represent 8 (so it can fit in 3 bits)
        // but here we want the actual number of bits in the byte
        if (bits_in_first_byte == 0) begin
            bits_in_first_byte = 8;
        end

        if (bits_in_last_byte == 0) begin
            bits_in_last_byte = 8;
        end

        bits = {};
        last_byte = data.size - 1;
        foreach (data[i]) begin
            int bits_to_send;
            bits_to_send = (i == 0)         ? bits_in_first_byte :
                           (i == last_byte) ? bits_in_last_byte  :
                                              8;

            // LSb first
            for (int b = 0; b < bits_to_send; b++) begin
                bits.push_back(data[i][b]);
            end
        end

        return bits;
    endfunction

    // ------------------------------------------------------------------------
    // external helper functions
    // ------------------------------------------------------------------------

    // Generates a queue of sequences that do not contain X -> Z or Y -> Y sequences
    // nor does it contain EOCs other than one at the end.
    // It starts with Z (SOC) and ends in ZYY or XYY (EOC + IDLE)
    //
    // resulting sequence queue will be of length len or len+1
    // we could find a way of making it exactly len sequences long
    // but I don't think there's a need to.
    //
    // Min len is 2, which will result in a ZYY
    function PCDBitSequenceQueue generate_valid_sequence_queue (int len);
        PCDBitSequenceQueue res;
        res.delete;

        // first frame is always a Z
        res.push_back(PCDBitSequence_Z);
        for (int i = 0; i < len - 2; i++) begin
            PCDBitSequence nextSeq;
            PCDBitSequence allowed [$];
            // valid sequences depend on previous
            // in no case should we generate PCDBitSequence_ERROR
            // X -> Z, Y -> Y, Z -> Y are not allowed
            case (res[$])
                PCDBitSequence_X: allowed = '{PCDBitSequence_X, PCDBitSequence_Y};
                PCDBitSequence_Y: allowed = '{PCDBitSequence_X, PCDBitSequence_Z};
                PCDBitSequence_Z: allowed = '{PCDBitSequence_X, PCDBitSequence_Z};
            endcase

            std::randomize(nextSeq) with {nextSeq inside {allowed};};
            res.push_back(nextSeq);
        end

        // Then we want the Ys, so we go idle
        // either need to add one or two Ys, depending if the last sequence is already a Y
        if (res[$] != PCDBitSequence_Y) begin
            res.push_back(PCDBitSequence_Y);
        end
        res.push_back(PCDBitSequence_Y);

        return res;
    endfunction

    function bit_queue generate_bit_queue (int len);
        bit_queue res;
        res.delete;

        // no restrictions here
        for (int i = 0; i < len; i++) begin
            res.push_back($urandom_range(1));
        end

        return res;
    endfunction

    function byte_queue generate_byte_queue (int len);
        byte_queue res;
        res.delete;

        // no restrictions here
        for (int i = 0; i < len; i++) begin
            res.push_back($urandom_range(255));
        end

        return res;
    endfunction

    function PCDBitSequenceQueue convert_bit_queue_to_sequence_queue (logic bits[$]);
        // build up a PCDBitSequence queue
        PCDBitSequence seqs[$];
        seqs.delete;

        // See ISO/IEC 14443-2:2106 section 8.1.3.1

        // Start of comms
        seqs.push_back(PCDBitSequence_Z);

        // data
        foreach (bits[i]) begin
            if (bits[i]) begin
                // 1 -> X
                seqs.push_back(PCDBitSequence_X);
            end
            else begin
                // 0 -> if previous sequence was a Y or a Z, then we send Z. Otherwise Y
                if (seqs[$] == PCDBitSequence_X) begin
                    seqs.push_back(PCDBitSequence_Y);
                end
                else begin
                    seqs.push_back(PCDBitSequence_Z);
                end
            end
        end

        // end of comms: logic '0' followed by sequence Y
        if (seqs[$] == PCDBitSequence_X) begin
            seqs.push_back(PCDBitSequence_Y);
        end
        else begin
            seqs.push_back(PCDBitSequence_Z);
        end

        seqs.push_back(PCDBitSequence_Y);

        // note: sequence_decode requires two sequence Ys in a row to go idle
        //       whereas we could be finishing with YY or ZY.
        //       This is fine because send_sequence_queue enforces 5 bit times
        //       of idle (sequence Y) at the end of the queue.

        return seqs;
    endfunction

    function bit_queue add_parity_to_bit_queue (logic bits[$], int first_parity_after_bits=8);
        // create a new bit queue with the parity bits in
        automatic bit_queue new_bits    = '{};
        automatic int bit_count         = 0;
        automatic logic parity          = 1'b1;
        automatic int parity_after_bits = first_parity_after_bits;

        if (parity_after_bits == 0) begin
            parity_after_bits = 8;
        end

        // see ISO/IEC 14443-3:2016 section 6.2.3.2.1
        // parity is set so that the number of 1s is odd in each byte

        foreach (bits[i]) begin
            new_bits.push_back(bits[i]);

            if (bits[i] == 1) begin
                parity = !parity;
            end

            bit_count++;
            if (bit_count == parity_after_bits) begin
                bit_count = 0;
                new_bits.push_back(parity);
                parity              = 1'b1;
                parity_after_bits   = 8;
            end
        end

        return new_bits;
    endfunction

    function bit_queue convert_message_to_bit_queue_for_tx (logic [7:0] data [$], int bits_in_first_byte=8);
        automatic int bits_in_last_byte = 8;
        if (data.size == 1) begin
            // only one byte
            bits_in_last_byte = bits_in_first_byte;
        end
        return convert_message_to_bit_queue_internal (data, bits_in_first_byte, bits_in_last_byte);
    endfunction

    function bit_queue convert_message_to_bit_queue_for_rx (logic [7:0] data [$], int bits_in_last_byte=8);
        automatic int bits_in_first_byte = 8;
        if (data.size == 1) begin
            // only one byte
            bits_in_first_byte = bits_in_last_byte;
        end
        return convert_message_to_bit_queue_internal (data, bits_in_first_byte, bits_in_last_byte);
    endfunction

    function logic [15:0] calculate_crc (logic [7:0] data[$]);
        logic [15:0] crc;
        crc = 16'h6363;

        foreach (data[i]) begin
            // convert to 16 bit
            logic [15:0] ch;
            ch = {8'd0, data[i]};

            ch = ch ^ (crc & 16'h00FF);
            ch = (ch ^ ({ch[11:0], 4'd0} & 16'h00FF));

            crc = {8'd0, crc[15:8]} ^ {ch[7:0], 8'd0} ^ {ch[12:0], 3'd0} ^ {4'd0, ch[15:4]};
        end

        return crc;
    endfunction

    function byte_queue add_crc_to_message (logic [7:0] data [$]);
        logic [15:0] crc;

        // calculate the CRC
        crc = calculate_crc(data);

        // add it to the data to send in little endien byte order
        data.push_back(crc[7:0]);
        data.push_back(crc[15:8]);

        return data;
    endfunction

endpackage
