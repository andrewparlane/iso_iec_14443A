/***********************************************************************
        File: iso14443a_pkg.sv
 Description: Common types and values
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

package ISO14443A_pkg;

    // ========================================================================
    // Bit sequences for PCD to PICC comms
    // See ISO/IEC 14443-2:2016 section 8.1.3.1
    // ========================================================================
    typedef enum logic [1:0]
    {
        PCDBitSequence_ERROR,   // Invalid timings (or X -> Z)
        PCDBitSequence_X,       // pause frame in second half of bit time
        PCDBitSequence_Y,       // no pause frame for one bit time
        PCDBitSequence_Z        // pause frame at the start of bit time
    } PCDBitSequence;

    // ========================================================================
    // UID Sizes
    // See ISO/IEC 14443-3:2016 section 6.5.4
    // ========================================================================
    typedef enum logic [1:0]
    {
        UIDSize_SINGLE,
        UIDSize_DOUBLE,
        UIDSize_TRIPLE
    } UIDSize;

    function automatic int get_uid_bits(UIDSize size);
        case (size)
            UIDSize_SINGLE: return  4 * 8;
            UIDSize_DOUBLE: return  7 * 8;
            UIDSize_TRIPLE: return 10 * 8;

            // I wish there was a way for synthesis time asserts
            // I'm adding something to the initialisation module
            // to error if this returns 0 hopefully that'll catch any errors
            default:        return  0;
        endcase
    endfunction

    // see ISO/IEC 14443-3:2016 section 6.5.4
    localparam logic [7:0]  CASCADE_TAG     = 8'h88;

    // ========================================================================
    // PCD -> PICC Messages
    // ========================================================================

    // short frames, see ISO/IEC 14443-3:2016 section 6.4.1
    localparam logic [6:0]  REQA            = 7'h26;
    localparam logic [6:0]  WUPA            = 7'h52;

    // standard frames, see ISO/IEC 14443-3:2016 section 6.4.3
    // Note: received LSByte first
    localparam logic [15:0] HLTA            = 16'h0050;    // 0x50, 0x00

    // AC frames, see ISO/IEC 14443-3:2016 section 6.5.3.2
    localparam logic [7:0]  SEL1            = 8'h93;
    localparam logic [7:0]  SEL2            = 8'h95;
    localparam logic [7:0]  SEL3            = 8'h97;

    // Part 4 commands, see ISO/IEC 14443-4:2016 sections 5.1/5.3
    localparam logic [7:0]  RATS            = 8'hE0;
    localparam logic [3:0]  PPSS            = 4'hD;

    // ========================================================================
    // PICC -> PCD Messages
    // ========================================================================

    // ATQA, see ISO/IEC 14443-3:2016 section 6.2.5.1
    // I don't really understand the point of this message.
    // If there are two tags a collision will occur unless they happen to be of
    // the same UID size and use the same bit frame anticollision field.
    // the bit frame anticollision field is arbitrary. We use bit 2.
    // defined as a function so we can pass UID_SIZE in. Will still be constant
    function automatic logic [15:0] ATQA(UIDSize size);
        case (size)
            UIDSize_SINGLE: return 16'h0004;
            UIDSize_DOUBLE: return 16'h0044;
            default:        return 16'h0084;
        endcase
    endfunction

    // SAK, see ISO/IEC 14443-3:2016 section 6.5.3.4
    // there are two options here, UID complete and UID not complete.
    // send the latter when we have received a SELECT for us, but it just
    // finishes the cascade level and not the entire UID.
    // We support ISO/IEC 14443-4, and so bit 5 is set when bit 2 is cleared
    localparam logic [7:0] SAK_UID_COMPLETE     = 8'h20;
    localparam logic [7:0] SAK_UID_NOT_COMPLETE = 8'h04;

    // part 4 commands
    // these have the CID, NAD and the block num set to 0, set those bits if needed
    localparam logic [7:0]  S_DESELECT      = 8'b11000010;
    localparam logic [7:0]  S_PARAMETERS    = 8'b11110000;
    localparam logic [7:0]  R_ACK           = 8'b10100010;
    localparam logic [7:0]  I_NO_CHAINING   = 8'b00000010;

    // ========================================================================
    // Anticollision / select structs
    // ========================================================================

    // AC and SELECT commands are the same message.
    // We call them AC if the PCD only sends part of it, and the PICC replies with the rest
    // We call them SELECT if the PCD sends all of it + CRC
    typedef struct packed
    {
        // must add up to 8 bits
        logic       rsvd1;
        logic [2:0] bytes;
        logic       rsvd2;
        logic [2:0] bits;
    } NVB;

    typedef struct packed
    {
        // must add up to 40 bits
        logic [31:0] uid;
        logic [7:0] bcc;
    } UIDData;

    typedef struct packed
    {
        // must add up to 56 bits
        logic [7:0] cascadeLevel;
        NVB         nvb;
        UIDData     uid_data;
    } AntiCollisionSelectCommand;

endpackage
