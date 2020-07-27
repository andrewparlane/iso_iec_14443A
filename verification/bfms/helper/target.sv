/***********************************************************************
        File: target.sv
 Description: A class to store details about a particular PICC
              for use with the Sequence class
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

package target_pkg;

    import std_block_address_pkg::StdBlockAddress;

    class Target;

        // The PICC's UID (public, because we want to use class members)
        uid_pkg::UID                uid;

        // The current select level for use with initialisation
        protected int               select_level;

        // Block nums
        protected logic             pcd_block_num;
        protected logic             picc_block_num; // we maintain this only so we can test it is as expected

        // The StdBlockAddress, stores CID, has_cid, power
        protected StdBlockAddress   our_addr;

        function new(uid_pkg::UID _uid);
            uid             = _uid;
            select_level    = 0;
            our_addr        = StdBlockAddress::new_no_cid_no_nad();
            initialise_block_nums();
        endfunction

        virtual function void set_select_level(int level);
            select_level = level;
        endfunction

        virtual function int get_select_level;
            return select_level;
        endfunction

        virtual function void initialise_block_nums;
            // ISO/IEC 14443-4:2016 section 7.5.4, Rule A
            // The PCD block number shall be initialized to 0 for each activated PICC.
            pcd_block_num = 1'b0;
            //$display("TB: Init pcd_block_num to %b", pcd_block_num);

            // Rule C
            // The PICC block number shall be initialised to 1 at activation
            picc_block_num = 1'b1;
        endfunction

        virtual function logic get_picc_block_num;
            return picc_block_num;
        endfunction

        virtual function logic get_pcd_block_num;
            return pcd_block_num;
        endfunction

        virtual function logic picc_and_pcd_block_nums_are_equal;
            return pcd_block_num == picc_block_num;
        endfunction

        virtual function void toggle_picc_block_num;
            picc_block_num = !picc_block_num;
        endfunction

        virtual function void toggle_pcd_block_num;
            pcd_block_num = !pcd_block_num;
        endfunction

        virtual function void set_cid(logic supports_cid, int cid);
            our_addr.has_cid    = supports_cid;
            our_addr.cid        = cid;
        endfunction

        virtual function logic get_supports_cid;
            return our_addr.has_cid;
        endfunction

        virtual function logic [3:0] get_cid;
            return our_addr.cid;
        endfunction

        virtual function void set_power(logic [1:0] power);
            our_addr.power = power;
        endfunction

        virtual function logic [1:0] get_power;
            return our_addr.power;
        endfunction

        virtual function StdBlockAddress get_addr;
            return our_addr;
        endfunction

        virtual function StdBlockAddress get_reply_addr(StdBlockAddress send_addr);
            // The PICC responds with a CID noly if it is addressed with a CID.
            // note: we don't check here, that the message was addressed to us.
            if (send_addr.has_cid) begin
                return our_addr;
            end
            else begin
                return StdBlockAddress::new_no_cid_no_nad;
            end
        endfunction

        virtual function logic is_for_us(StdBlockAddress target_addr);
            // Since this IP core currently doesn't support NADs, and
            // ISO/IEC 14443-4:2016 section 7.1.2.3 states:
            // when the PICC does not support the NAD, it shall ignore any block containing the NAD.
            if (target_addr.has_nad) begin
                return 1'b0;
            end

            // ISO/IEC 14443-4:2016 section 7.1.2.2 states:
            // A PICC, which does not support a CID
            // - shall ignore any blocks containing a CID
            if (!our_addr.has_cid && target_addr.has_cid) begin
                return 1'b0;
            end
            else begin
                // A PICC, which does support a CID
                // - shall respond to blocks containing its CID by using its CID,
                // - shall ignore blocks containing other CIDs, and
                // - shall, in case its CID is 0, respond also to blocks containing no CID by using no CID.
                if (target_addr.has_cid) begin
                    // has a cid, so only respond if it's our CID
                    return (target_addr.cid == our_addr.cid);
                end
                else begin
                    // doesn't have a CID, so only respond if our CID is 0
                    return (our_addr.cid == 0);
                end
            end
        endfunction

    endclass

endpackage
