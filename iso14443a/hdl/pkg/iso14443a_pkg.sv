/***********************************************************************
        File: iso14443a_pkg.sv
 Description: Common types and values
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

package ISO14443A_pkg;

    // ========================================================================
    // Bit sequences for PCD to PICC comms
    // See ISO/IEC 14443-2:2016 section 8.1.3.1
    // ========================================================================
    typedef enum
    {
        PCDBitSequence_ERROR,   // Invalid timings (or X -> Z)
        PCDBitSequence_X,       // pause frame in second half of bit time
        PCDBitSequence_Y,       // no pause frame for one bit time
        PCDBitSequence_Z        // pause frame at the start of bit time
    } PCDBitSequence;

endpackage
