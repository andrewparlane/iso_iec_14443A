/***********************************************************************
        File: uid.sv
 Description: A class to store the UID of a PICC
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

package uid_pkg;

    import ISO14443A_pkg::UIDSize;
    import ISO14443A_pkg::UIDSize_SINGLE;
    import ISO14443A_pkg::UIDSize_DOUBLE;
    import ISO14443A_pkg::UIDSize_TRIPLE;
    import ISO14443A_pkg::CASCADE_TAG;
    import ISO14443A_pkg::get_uid_bits;

    // can call .randomize() on this class
    class UID;

        // A single UID level used for a select / AC
        typedef logic [31:0]    UIDLevel;

        // triple UID size has 10 bytes = 80 bits
        protected rand logic [79:0]     uid;                // marked as rand for use with randomize
        protected UIDSize               size;
        protected UIDLevel              uid_level   [$];

        // constraints on randomisation (doesn't apply if manually set with new())
        // ISO/IEC 14443-3:2016 section 6.5.4 states that UID0 can't be 8'h88 for single UIDs
        // and that UID3 can't be 8'h88 for double UIDs. 8'h88 == CASCADE_TAG

        constraint cascade_tag_constraint
        {
            (size == UIDSize_SINGLE)    -> (uid[7:0]    != CASCADE_TAG);
            (size == UIDSize_DOUBLE)    -> (uid[31:24]  != CASCADE_TAG);
        }

        function new(logic [79:0] _uid, UIDSize _size);
            uid         = _uid;
            size        = _size;

            update_internals;
        endfunction

        // 4 bytes
        static function UID new_single_uid(logic [31:0] _uid);
            automatic UID res = new({47'bX, _uid}, UIDSize_SINGLE);
            return res;
        endfunction

        // 7 bytes
        static function UID new_double_uid(logic [55:0] _uid);
            automatic UID res = new({23'bX, _uid}, UIDSize_DOUBLE);
            return res;
        endfunction

        // 10 bytes
        static function UID new_triple_uid(logic [79:0] _uid);
            automatic UID res = new(_uid, UIDSize_TRIPLE);
            return res;
        endfunction

        virtual protected function void update_internals;
            uid_level = '{};

            if (size == UIDSize_SINGLE) begin
                // first level is the entire UID
                uid_level.push_back(uid[31:0]);

                // set unused bits to X
                uid[79:32] = 'x;
            end
            else begin // double or triple
                // first level is the first 3 bytes with the cascade tag
                uid_level.push_back({uid[23:0], CASCADE_TAG});

                if (size == UIDSize_DOUBLE) begin
                    // second level is the remaining 4 bytes
                    uid_level.push_back(uid[55:24]);

                    // set unused bits to X
                    uid[79:56] = 'x;
                end
                else begin // triple
                    // second level is the next 3 bytes with the cascade tag
                    uid_level.push_back({uid[47:24], CASCADE_TAG});

                    // third level is the last 4 bytes
                    uid_level.push_back(uid[79:48]);
                end
            end
        endfunction

        function void post_randomize;
            update_internals;
        endfunction

        virtual function string to_string;
            string res;
            res = $sformatf("size: %s, uid: %b (%x), levels: %p", size.name, uid, uid, uid_level);
            return res;
        endfunction

        virtual function UIDSize get_size;
            return size;
        endfunction

        virtual function logic [79:0] get_full_uid;
            return uid;
        endfunction

        virtual function int get_num_levels;
            case (size)
                UIDSize_SINGLE: return 1;
                UIDSize_DOUBLE: return 2;
                UIDSize_TRIPLE: return 3;
                default:        $fatal(0, "size invalid");
            endcase
        endfunction

        virtual function UIDLevel get_level(int level);
            return uid_level[level];
        endfunction

        virtual function logic compare(int level, int num_bits, UIDLevel data);
            if (level >= get_num_levels) begin
                return 1'b0;
            end

            // compare num_bits for this level
            // is there a better way to do this than bit by bit?
            for (int i = 0; i < num_bits; i++) begin
                if (data[i] != uid_level[level][i]) begin
                    return 1'b0;
                end
            end
            return 1'b1;
        endfunction
    endclass

    // can call .randomize() on this class
    class FixedSizeUID
    #(
        parameter UIDSize                       UID_SIZE,
        // Our IP core has parameters to split the UID into two parts
        // A fixed upper part and a variable lower part.
        parameter int                           UID_FIXED_BITS  = 0,
        parameter logic [UID_FIXED_BITS:0]      UID_FIXED               // note: not -1, so we can do UID_FIXED_BITS == 0
    )
    extends UID;

        localparam int UID_BITS             = get_uid_bits(UID_SIZE);
        localparam int UID_VARIABLE_BITS    = UID_BITS - UID_FIXED_BITS;

        // constrain the fixed bits for use with .randomize
        constraint uid_fixed_constraint
        {
            (UID_FIXED_BITS != 0) -> (uid[UID_BITS - 1:UID_BITS - UID_FIXED_BITS] == UID_FIXED[UID_FIXED_BITS-1:0]);
        }

        function new(logic [UID_VARIABLE_BITS-1:0] _uid);
            super.new(80'((UID_FIXED_BITS != 0)
                                ? {UID_FIXED[UID_FIXED_BITS-1:0], _uid}
                                : _uid),
                      UID_SIZE);
        endfunction

        virtual function logic [UID_BITS-1:0] get_uid;
            return uid[UID_BITS-1:0];
        endfunction

        virtual function string to_string;
            string res = "";
            if (UID_FIXED_BITS != 0) begin
                res = $sformatf("Fixed: %b (%x), ",
                                UID_FIXED[UID_FIXED_BITS-1:0],
                                UID_FIXED[UID_FIXED_BITS-1:0]);
            end
            res = {res, $sformatf("uid: %b (%x), levels: %p",
                                  uid[UID_BITS-1:0],
                                  uid[UID_BITS-1:0],
                                  uid_level)};
            return res;
        endfunction

    endclass

endpackage
