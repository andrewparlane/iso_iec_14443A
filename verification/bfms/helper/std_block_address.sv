/***********************************************************************
        File: std_block_address.sv
 Description: A class to encapsulate CID and NAD info
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

package std_block_address_pkg;

    class StdBlockAddress;
        // The "address" of a STD block depends on the CID (which card / tag)
        // and the NAD (which node in that tag)

        // CID
        logic       has_cid;
        logic [3:0] cid;
        logic [1:0] power;      // The CID field has 2 bits of power info. Should be 2'b00 for Rx

        // NAD - only valid in STD I-blocks
        logic       has_nad;
        logic [7:0] nad;

        function new (logic _has_cid,   logic [3:0] _cid,   logic [1:0] _power,
                      logic _has_nad,   logic [7:0] _nad);
            has_cid     = _has_cid;
            cid         = _cid;
            power       = _power;
            has_nad     = _has_nad;
            nad         = _nad;
        endfunction

        static function StdBlockAddress new_no_cid_no_nad;
            automatic StdBlockAddress res = new(0, 0, 0, 0, 0);
            return res;
        endfunction

        static function StdBlockAddress new_cid_no_nad(logic [3:0] _cid, logic [1:0] _power);
            automatic StdBlockAddress res = new(1'b1, _cid, _power, 0, 0);
            return res;
        endfunction

        static function StdBlockAddress new_nad_no_cid(logic [7:0] _nad);
            automatic StdBlockAddress res = new(0, 0, 0, 1'b1, _nad);
            return res;
        endfunction

        static function StdBlockAddress new_cid_nad(logic [3:0] _cid, logic [1:0] _power,
                                                    logic [7:0] _nad);
            automatic StdBlockAddress res = new(1'b1, _cid, _power, 1'b1, _nad);
            return res;
        endfunction

    endclass

endpackage
