/***********************************************************************
        File: iso14443a_pcd_to_picc_comms_generator.sv
 Description: Generates the clock and emulates PCD to PICC comms
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

// This module generates an emulated version of the clk and pause_n outputs
// of the ISO/IEC 14443A analogue IP core for use with simulations.
// Some of the variables in here should be tweaked carefully to mimic the
// actual analogue IP core as closely as possible.

// Variables:
//      pause_n_asserts_after_ps    - the pause_n output asserts a number of ps after the "PCD" decides to send a pause.
//      pause_n_deasserts_after_ps  - it deasserts a number of ps after the "PCD" decides to stop sending the pause.
//      clock_stops_after_ps        - the clk output stops a number of ps after the "PCD" decides to send a pause.
//      clock_starts_after_ps       - it starts again a number of ps after the "PCD" decides to stop sending the pause.
//      pause_len                   - The number of ticks of the carrier wave in a pause.
//      bit_time                    - The number of ticks of the carrier wave in a bit
//      sequence_x_pause_start_time - When does the pause start in the bit time for sequence X
//      sequence_z_pause_start_time - when does the pause start in the bit time for sequence Z

module iso14443a_pcd_to_picc_comms_generator
#(
    // The half period is rounded to the nearest ps
    // so the resulting clock not perfectly 13.56MHz
    parameter CLOCK_FREQ_HZ = 13560000  // 13.56MHz
)
(
    output logic clk,       // Note: the clk stops during pauses (see clock_stops_after_ps and clock_starts_after_ps)
    output logic pause_n,   // Note: you can not rely on this to be synchronised to a clock edge
    output logic sending    // Indicates that we are sending something
);

    // Calculate our clock period in ps
    localparam CLOCK_PERIOD_PS = 1000000000000.0 / CLOCK_FREQ_HZ;

    // ------------------------------------------------------------------------
    // Comments about how this code works
    // ------------------------------------------------------------------------

    // When the PCD wants to send data it uses on-off-keying (OOK) to send a "pause frame"
    // Meaning the PICC detects the carrier wave reducing to < 5% of it's former value,
    // for a period of time.

    // Since the PICC generates it's clock based off the carrier wave the PICC's clock
    // halts during pause frames.

    // The PICC also contains a pause detector which asserts when it detects we are in a
    // pause frame.

    // When the clock halts / starts again, and when the pause is detected / end of pause
    // is detected, depends on the analogue part of the PICC implementation. Here I emulate
    // the PCD deciding to send data with the pcd_pause_n signal.
    // The clock stops clock_stops_after_ps ps after that signal asserts.
    // The pause_n signal asserts pause_n_asserts_after_ps ps that signal asserts.
    // The clock starts again clock_starts_after_ps ps after that signal deasserts
    // The pause_n signal deasserts pause_n_deasserts_after_ps ps after that signal deasserts.
    // A range of these values should be tested to ensure correct functioning of the RTL,
    // and the analogue core should ensure that the actual implementation is within the tested
    // range.

    // TODO: define this range and write down analogue spec requirements
    // How do we determine this?
    //      Determine worst case envelope profile for the pause that meets the spec
    //      and run tests using that to figure out what the max delays in the analogue
    //      core can be?
    //      Or just run sims of the analogue core and use a largish range of values around
    //      the found results?

    // ------------------------------------------------------------------------
    // Default values for variables
    // ------------------------------------------------------------------------
    localparam default_pause_len = 32;

    // ------------------------------------------------------------------------
    // Variables
    // ------------------------------------------------------------------------

    // looking at figure 5.11 in Fabricio's thesis we see that pause_n asserts
    // ~1 us after the PCD starts the pause, and deasserts it ~150 ns after
    // the PCD ends the pause
    int pause_n_asserts_after_ps    = 1 * 1000 * 1000;  // 1us
    int pause_n_deasserts_after_ps  =      150 * 1000;  // 150 ns

    // I currently have no data on how long this takes. It depends on the switching point
    // of the inverters in the clock generator, and how long it takes the PCD's output to
    // reach that point. Picking values semi at random.
    int clock_stops_after_ps        = 500 * 1000; // 500 ns
    int clock_starts_after_ps       = 100 * 1000; // 100 ns

    // These determine the timing of pauses / sequences (in ticks)
    // pause_len depends on the PCD and the analogue implementation of the PICC
    // The others are constants defined in ISO/IEC 14443-2.
    // I allow them to be changed in order to test the flexibility of my implementation.
    int pause_len                   = default_pause_len;
    int bit_time                    = 128;
    int sequence_x_pause_start_time = 64;
    int sequence_z_pause_start_time = 0;

    // ------------------------------------------------------------------------
    // PCD clk
    // ------------------------------------------------------------------------

    // This is a simulated version of the clock that the PCD uses
    // it's constant at CLOCK_FREQ_HZ
    logic pcd_clk;
    initial begin
        pcd_clk <= 0;
        forever begin
            #(int'(CLOCK_PERIOD_PS/2));
            pcd_clk <= ~pcd_clk;
        end
    end

    // ------------------------------------------------------------------------
    // pause_n generation
    // ------------------------------------------------------------------------

    // We set this to emulate the PCD sending a pause
    logic pcd_pause_n;
    initial pcd_pause_n = 1;

    // The PICC's pause_n signal asserts / deasserts some delay after the pcd_pause_n
    // signal, so just use the #(rise_delay, fall_delay) syntax of verilog.
    // note: we can't initialise pause_n because the simulator doesn't like that
    //       it's assigned with an assign and in an initial, so just make sure
    //       that the resret is longer than pause_n_deasserts_after_ps
    assign #(pause_n_deasserts_after_ps, pause_n_asserts_after_ps) pause_n = pcd_pause_n;

    // ------------------------------------------------------------------------
    // PICC clock generation
    // ------------------------------------------------------------------------

    // We also have the stop_clk internal signal which behaves in the same way
    logic stop_clk;
    assign #(clock_stops_after_ps, clock_starts_after_ps) stop_clk = !pcd_pause_n;

    // generate the PICC's clock
    // Note: this clock can be in phase to the pcd_clk or 180 degrees out of phase.
    //       and it can change between them, depending on when the clock stops
    //       and starts. This matches the analogue implementation of the clock
    //       recovery block.
    initial begin
        clk <= 0;
        forever begin
            #(int'(CLOCK_PERIOD_PS/2));
            if (!stop_clk) begin
                clk <= ~clk;
            end
        end
    end

    // ------------------------------------------------------------------------
    // Debug signals
    // ------------------------------------------------------------------------

    // Run a counter to count ticks in each bit time
    // and pulse a signal at the start of each bit
    logic run_bit_time_counter = 0;
    int bit_time_counter;

    always_ff @(posedge pcd_clk) begin
        if (run_bit_time_counter) begin
            if (bit_time_counter == (bit_time - 1)) begin
                bit_time_counter    <= 0;
            end
            else begin
                bit_time_counter    <= bit_time_counter + 1'd1;
            end
        end
        else begin
            bit_time_counter <= 0;
        end
    end

    logic start_of_bit;
    assign start_of_bit = (bit_time_counter == 0) && run_bit_time_counter;

    // ------------------------------------------------------------------------
    // Variable get / set functions
    // ------------------------------------------------------------------------

    function void set_delays(int new_pause_n_asserts_after_ps,
                             int new_pause_n_deasserts_after_ps,
                             int new_clock_stops_after_ps,
                             int new_clock_starts_after_ps);
        pause_n_asserts_after_ps    = new_pause_n_asserts_after_ps;
        pause_n_deasserts_after_ps  = new_pause_n_deasserts_after_ps;
        clock_stops_after_ps        = new_clock_stops_after_ps;
        clock_starts_after_ps       = new_clock_starts_after_ps;
    endfunction

    function void set_pause_length(int new_pause_len);
        pause_len = new_pause_len;
    endfunction

    function void set_bit_length(int new_bit_time);
        bit_time = new_bit_time;
    endfunction

    function void set_sequence_start_times(int new_sequence_x_pause_start_time,
                                           int new_sequence_z_pause_start_time);
        sequence_x_pause_start_time = new_sequence_x_pause_start_time;
        sequence_z_pause_start_time = new_sequence_z_pause_start_time;
    endfunction

    // ------------------------------------------------------------------------
    // internal functions / tasks
    // All of these should only be called on the posedge of pcd_clk
    // noting that this does not equate to posedge clk
    // ------------------------------------------------------------------------

    task do_pause;
        pcd_pause_n = 0;
        repeat (pause_len) @(posedge pcd_clk);
        pcd_pause_n = 1;
    endtask

    task send_sequence_x;
        repeat (sequence_x_pause_start_time) @(posedge pcd_clk);
        do_pause;
        repeat (bit_time - sequence_x_pause_start_time - pause_len) @(posedge pcd_clk);
    endtask

    task send_sequence_y;
        repeat (bit_time) @(posedge pcd_clk);
    endtask

    task send_sequence_z;
        repeat (sequence_z_pause_start_time) @(posedge pcd_clk);
        do_pause;
        repeat (bit_time - sequence_z_pause_start_time - pause_len) @(posedge pcd_clk);
    endtask

    task send_sequence (PCDBitSequence seq);
        case (seq)
            PCDBitSequence_ERROR:   $warning("PCDBitSequence_ERROR is not supported here");
            PCDBitSequence_X:       send_sequence_x;
            PCDBitSequence_Y:       send_sequence_y;
            PCDBitSequence_Z:       send_sequence_z;
        endcase
    endtask

    // ------------------------------------------------------------------------
    // Helper types (so we can return arrays from functions
    // ------------------------------------------------------------------------
    typedef PCDBitSequence  PCDBitSequenceQueue [$];
    typedef bit             bit_queue           [$];
    typedef bit [7:0]       byte_queue          [$];

    // ------------------------------------------------------------------------
    // external helper functions
    // ------------------------------------------------------------------------

    // Generates a queue of sequences that do not contain X -> Z or Y -> Y sequences
    // It may however contain a Z -> Y, which indicates an end of frame by frame_decode
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
            // valid sequences depend on previous
            // in no case should we generate PCDBitSequence_ERROR
            // Note: we could use std::randomize(nextSeq) with {nextSeq inside {...};};
            //       but I don't have the modelsim license for that.
            //       so we just repeat until we get a valid result
            while (1) begin
                case ($urandom_range(2))
                    0: nextSeq = PCDBitSequence_X;
                    1: nextSeq = PCDBitSequence_Y;
                    2: nextSeq = PCDBitSequence_Z;
                endcase

                if (((res[$] == PCDBitSequence_X) && (nextSeq == PCDBitSequence_Z)) ||
                    ((res[$] == PCDBitSequence_Y) && (nextSeq == PCDBitSequence_Y))) begin
                    // invalid transition, try again
                    continue;
                end
                else begin
                    // we're good
                    break;
                end
            end

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

    function PCDBitSequenceQueue convert_bit_queue_to_sequence_queue (bit bits[$]);
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

    function bit_queue add_parity_to_bit_queue (bit bits[$]);
        // create a new bit queue with the parity bits in
        bit_queue new_bits;
        int bit_count;
        bit parity;

        // see ISO/IEC 14443-3:2016 section 6.2.3.2.1
        // parity is set so that the number of 1s is odd in each byte

        new_bits = {};
        bit_count = 0;
        parity = 1;
        foreach (bits[i]) begin
            new_bits.push_back(bits[i]);

            if (bits[i] == 1) begin
                parity = !parity;
            end

            bit_count++;
            if (bit_count == 8) begin
                bit_count = 0;
                new_bits.push_back(parity);
                parity = 1;
            end
        end

        return new_bits;
    endfunction

    function bit_queue convert_message_to_bit_queue (bit [7:0] data [$], int bits_in_last_byte);
        // build a bit queue
        bit_queue bits;
        int last_byte;

        // in some places we use 0 to represent 8 (so it can fit in 3 bits)
        // but here we want the actual number of bits in the last byte
        if (bits_in_last_byte == 0) begin
            bits_in_last_byte = 8;
        end

        bits = {};
        last_byte = data.size - 1;
        foreach (data[i]) begin
            int bits_to_send;
            bits_to_send = (i == last_byte) ? bits_in_last_byte : 8;

            // LSb first
            for (int b = 0; b < bits_to_send; b++) begin
                bits.push_back(data[i][b]);
            end
        end

        return bits;
    endfunction

    function logic [15:0] calculate_crc (bit [7:0] data[$]);
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

    // little test to make sure the calculate_crc algorithm is correct
    initial begin
        crcTest1: assert (calculate_crc('{8'h0, 8'h0}) == 16'h1EA0) else $fatal(1, "calculate_crc test 1 failed");
        crcTest2: assert (calculate_crc('{8'h12, 8'h34}) == 16'hCF26) else $fatal(1, "calculate_crc test 2 failed");
    end

    function byte_queue add_crc_to_message (bit [7:0] data [$]);
        logic [15:0] crc;

        // calculate the CRC
        crc = calculate_crc(data);

        // add it to the data to send in little endien byte order
        data.push_back(crc[7:0]);
        data.push_back(crc[15:8]);

        return data;
    endfunction

    // ------------------------------------------------------------------------
    // external data sending tasks
    // Each of these tasks starts and ends with an @(posedge pcd_clk)
    // note that does not mean they end synchronised to @(posedge clk)
    // ------------------------------------------------------------------------

    // Note that sending a sequence X followed by sequence Z is an error.
    // and that sending two or more sequence Ys in a row will result in the
    // sequence_decode core going idle and reporting the next sequence as a Z
    // regardless of what you ask it to send.
    initial sending = 0;
    task send_sequence_queue (PCDBitSequence seqs[$]);
        // synch to posedge of pcd_clk
        @(posedge pcd_clk);
        run_bit_time_counter <= 1;

        sending              <= 1;
        foreach (seqs[i]) send_sequence(seqs[i]);
        sending              <= 0;

        // enforce a small time between frames (5 bit times)
        // to ensure that the decoder goes idle
        repeat(5*bit_time) @(posedge pcd_clk);
        run_bit_time_counter <= 0;
    endtask

    // Sends just the bits in the queue. It does not add parity bits in.
    task send_bit_queue_no_parity (bit bits[$]);
        PCDBitSequence seqs[$];
        seqs = convert_bit_queue_to_sequence_queue(bits);

        // send it
        send_sequence_queue(seqs);
    endtask

    // sends the bits in the queue plus the parity bits
    task send_bit_queue_with_parity (bit bits[$]);
        // add the parity bits to the queue
        bits = add_parity_to_bit_queue(bits);

        // send the new queue out
        send_bit_queue_no_parity(bits);
    endtask

    // bits_in_last_byte should be 1 - 8.
    // 8 would be a standard frame.
    // 1-7 would be a broken byte anticollision frame.
    // Special case is that if data only has one entry and bits_in_last_byte is 7
    // then it's a short frame
    // Note: parity bits are auto inserted after every full byte
    //       CRC is not auto inserted
    task send_message_no_crc (bit [7:0] data [$], int bits_in_last_byte);
        // build a bit queue
        bit bits[$];
        bits = convert_message_to_bit_queue(data, bits_in_last_byte);

        // do it
        send_bit_queue_with_parity(bits);
    endtask

    // Messages with CRCs have to be a whole number of bytes long
    task send_message_with_crc (bit [7:0] data [$]);
        data = add_crc_to_message(data);

        // send the message
        send_message_no_crc(data, 8);
    endtask

endmodule
