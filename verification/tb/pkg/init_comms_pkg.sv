/***********************************************************************
        File: init_comms_pkg.sv
 Description: Generate initialisation commands for PCD -> PICC comms
              and verify the replies.
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

package init_comms_pkg;

    import ISO14443A_pkg::UIDSize;
    import ISO14443A_pkg::UIDSize_SINGLE;
    import ISO14443A_pkg::UIDSize_DOUBLE;
    import ISO14443A_pkg::UIDSize_TRIPLE;

    // --------------------------------------------------------------
    // helper function to turn UID_SIZE_CODE into UIDSize
    // --------------------------------------------------------------

    // convert UID_SIZE_CODE to UIDSize (enum)
    // can't work out how to pass enums to VCS as parameters
    function UIDSize get_uid_size (int code);
        return (code == 0) ? UIDSize_SINGLE :
               (code == 1) ? UIDSize_DOUBLE :
                             UIDSize_TRIPLE;
    endfunction

    virtual class init_comms_class
    #(
        // What sized UID do we use?
        parameter UIDSize                       UID_SIZE,
        // How many UID bits are variable?
        parameter int                           UID_INPUT_BITS,
        // How many UID bits are fixed?
        parameter int                           UID_FIXED_BITS,
        // The fixed bits of the UID (defaults to 0)
        parameter logic [UID_FIXED_BITS-1:0]    UID_FIXED
    );

        // --------------------------------------------------------------
        // UID
        // --------------------------------------------------------------

        // Our entire UID is based on the fixed part passed as a parameter
        // and the variable part passed to the input port.
        // we make this 10 bytes wide for triple UIDs, even if we don't use UIDSize_TRIPLE
        // so that our randomisation can work easier

        local logic     [79:0]  tag_uid;
        local logic     [31:0]  sel_uid_level [3];

        function void set_uid(logic [UID_INPUT_BITS-1:0] uid_variable);
            if (UID_SIZE == UIDSize_SINGLE) begin
                tag_uid = {48'b0, UID_FIXED, uid_variable};
                sel_uid_level[0] = tag_uid[31:0];
                sel_uid_level[1] = '0;
                sel_uid_level[2] = '0;
            end
            else if (UID_SIZE == UIDSize_DOUBLE) begin
                tag_uid = {24'b0, UID_FIXED, uid_variable};
                sel_uid_level[0] = {tag_uid[23:0], 8'h88};
                sel_uid_level[1] = tag_uid[55:24];
                sel_uid_level[2] = '0;
            end
            else begin
                tag_uid = {UID_FIXED, uid_variable};
                sel_uid_level[0] = {tag_uid[23:0],  8'h88};
                sel_uid_level[1] = {tag_uid[47:24], 8'h88};
                sel_uid_level[2] = tag_uid[79:48];
            end
        endfunction

        function logic [79:0] get_uid;
            return tag_uid;
        endfunction

        function logic [UID_INPUT_BITS-1:0] randomise_uid;
            automatic logic [UID_INPUT_BITS-1:0] uid_variable;

            // we ideally want to do this
            /* if (UID_SIZE == UIDSize_SINGLE) begin
                std::randomize(uid_variable) with {tag_uid[7:0]     != 8'h88;};
            end
            else if (UID_SIZE == UIDSize_DOUBLE) begin
                std::randomize(uid_variable) with {tag_uid[7:0]     != 8'h88;
                                                   tag_uid[31:24]   != 8'h88; };
            end */

            // but VCS doesn't like that because tag_uid is not in the randomize list.
            // we can't do with {uid_variable[7:0] != ...} because we don't know how long uid_variable is
            // so lets just do it as a loop
            // Note: UID_FIXED can be set in such a way that this loop never exits.

            forever begin
                std::randomize(uid_variable);
                set_uid(uid_variable);

                // ISO/IEC 14443-3:2016 section 6.5.4 states that UID0 can't be 8'h88 for single UIDs
                // and that UID3 can't be 8'h88 for double UIDs.
                if (UID_SIZE == UIDSize_SINGLE) begin
                    if (tag_uid[7:0] != 8'h88) begin
                        break;
                    end
                end
                else if (UID_SIZE == UIDSize_DOUBLE) begin
                    if (tag_uid[31:24] != 8'h88) begin
                        break;
                    end
                end
                else begin
                    break;
                end
            end

            return uid_variable;
        endfunction

        function int get_num_sel_levels;
            case (UID_SIZE)
                UIDSize_SINGLE: return 1;
                UIDSize_DOUBLE: return 2;
                UIDSize_TRIPLE: return 3;
                default: $fatal(0, "invalid size");
            endcase
        endfunction

        // --------------------------------------------------------------
        // Data Structures
        // --------------------------------------------------------------

        // See ISO/IEC 14443-3:2016 section 6.3 PICC states
        typedef enum
        {
            //State_POWER_OFF,          // we don't use this, because if we are powered on
                                        // then there's an RF field, or it's just disabled
                                        // and we're about to power off
            State_IDLE,
            State_READY,
            State_ACTIVE,

            State_HALT,
            State_READY_STAR,
            State_ACTIVE_STAR

            //State_PROTOCOL            // we currently don't support the PROTOCOL state here
        } State;

        typedef enum
        {
            MsgType_REQA,
            MsgType_WUPA,
            MsgType_HLTA,
            MsgType_AC,
            MsgType_nAC,
            MsgType_SELECT,
            MsgType_nSELECT,
            MsgType_RANDOM,
            MsgType_ERROR
        } MsgType;

        typedef logic [7:0] byte_queue [$];

        typedef struct
        {
            byte_queue  data;
            int         bits_in_last_byte;
            logic       add_crc;
            logic       add_error;
        } MsgFromPCD;

        typedef struct
        {
            byte_queue  data;
            int         bits_in_first_byte;
            logic       has_crc;
        } MsgFromPICC;

        // --------------------------------------------------------------
        // Tasks / Functions that the child class must overwrite
        // --------------------------------------------------------------

        virtual task send_frame(MsgFromPCD msg);
            $fatal(0, "send_frame must be overwritten");
        endtask

        virtual task recv_frame(output MsgFromPICC msg, input logic expect_timeout=1'b0);
            $fatal(0, "recv_frame must be overwritten");
        endtask

        // could possible pass in rst and clock to this function then it wouldn't need to be virtual?
        virtual task do_reset;
            $fatal(0, "do_reset must be overwritten");
        endtask

        // this is common code but uses the path to the initialisation module's state
        // and I don't think I can pass that to a function. I can't pass the value either
        // as i'd need the type, which presumably varies per testbench since the path is different.
        // I might be able to use a system function with a string, like: $get_value(".tb.dut.state");?
        virtual function void check_state (State state);
            $fatal(0, "check_state must be overwritten");
        endfunction

        // --------------------------------------------------------------
        // PCD -> PICC message generation functions
        // --------------------------------------------------------------

        function MsgFromPCD generate_reqa;
            automatic MsgFromPCD res;
            res.data                = '{8'h26};
            res.bits_in_last_byte   = 7;
            res.add_crc             = 1'b0;
            res.add_error           = 1'b0;
            //$display("sending reqa %p", res);
            return res;
        endfunction

        function MsgFromPCD generate_wupa;
            automatic MsgFromPCD res;
            res.data                = '{8'h52};
            res.bits_in_last_byte   = 7;
            res.add_crc             = 1'b0;
            res.add_error           = 1'b0;
            //$display("sending wupa %p", res);
            return res;
        endfunction

        function MsgFromPCD generate_hlta (logic add_crc=1'b1);
            // we have add_crc so we can disable it to mimic a CRC fail
            automatic MsgFromPCD res;
            res.data                = '{8'h50, 8'h00};
            res.bits_in_last_byte   = 8;
            res.add_crc             = add_crc;
            res.add_error           = 1'b0;
            //$display("sending hlta %p", res);
            return res;
        endfunction

        int last_sent_uid_bits;
        function MsgFromPCD generate_ac_select (int level, int uid_bits, logic [31:0] uid, logic add_crc_if_select=1'b1, logic flip_last_bit=1'b0);
            // the AC/SELECT message is: sel, nvb, uid0, uid1, uid2, uid3, bcc
            automatic MsgFromPCD    res;
            automatic int           bytes_to_send       = 2 + $rtoi(real'(uid_bits) / 8.0); // $rtoi for truncate not round
            automatic logic [7:0]   bcc                 = uid[31:24] ^ uid[23:16] ^ uid[15:8] ^ uid[7:0];

            res.data.delete;
            res.bits_in_last_byte   = uid_bits % 8;
            res.add_crc             = add_crc_if_select && (uid_bits == 32);
            res.add_error           = 1'b0;

            // cache the number of sent bits for the AC reply
            last_sent_uid_bits      = uid_bits;

            if (uid_bits == 32) begin
                // send all of the UID so add BCC
                bytes_to_send++;
            end

            // SEL
            case (level)
                0: res.data.push_back(8'h93);
                1: res.data.push_back(8'h95);
                2: res.data.push_back(8'h97);
                default: $error("Invalsid level %d passed to send_ac_select", level);
            endcase

            // NVB
            res.data.push_back({4'(bytes_to_send), 4'(res.bits_in_last_byte)});

            // UID
            for (int i = uid_bits; i > 0; i-=8) begin
                res.data.push_back(uid[7:0]);
                uid = {8'h0, uid[31:8]};
            end

            // BCC
            if (uid_bits == 32) begin
                res.data.push_back(bcc);
            end

            if (flip_last_bit) begin
                res.data[$][7] = !res.data[$][7];
            end

            // send it
            //$display("sending AC/SELECT %p", res);
            return res;
        endfunction

        function MsgFromPCD generate_random;
            automatic MsgFromPCD    res;
            automatic int           bytes_to_send     = $urandom_range(1, 20);

            res.data.delete;
            res.bits_in_last_byte   = $urandom_range(0, 7);
            res.add_crc             = 1'($urandom);
            res.add_error           = 1'b0;

            for (int i = 0; i < bytes_to_send; i++) begin
                automatic logic [7:0] b;

                // don't let first byte be REQA, WUPA, HLTA[0], SELn
                if (i == 0) begin
                    std::randomize(b) with
                    {
                        b[6:0]  != 7'h26;
                        b[6:0]  != 7'h52;
                        b       != 8'h50;
                        b       != 8'h93;
                        b       != 8'h95;
                        b       != 8'h97;
                    };
                end
                else begin
                    std::randomize(b);
                end

                res.data.push_back(b);
            end

            //$display("sending random msg: %p", res);
            return res;
        endfunction

        function MsgFromPCD generate_error;
            automatic MsgFromPCD    res;
            automatic int           bytes_to_send     = $urandom_range(1, 20);

            res.data.delete;
            res.bits_in_last_byte   = $urandom_range(0, 7);
            res.add_crc             = 1'($urandom);
            res.add_error           = 1'b1;

            for (int i = 0; i < bytes_to_send; i++) begin
                automatic logic [7:0] b;
                std::randomize(b);
                res.data.push_back(b);
            end

            //$display("sending error %p", res);
            return res;
        endfunction

        function MsgFromPCD generate_msg(logic REQA, logic WUPA, logic HLTA,
                                         logic AC, logic nAC, logic SELECT, logic nSELECT,
                                         logic random, logic error);
            automatic MsgType       allowed [$] = '{};
            automatic MsgType       to_send;
            automatic int           level;
            automatic int           uid_bits;
            automatic logic [31:0]  invalid_uid;

            if (REQA) begin
                allowed.push_back(MsgType_REQA);
            end
            if (WUPA) begin
                allowed.push_back(MsgType_WUPA);
            end
            if (HLTA) begin
                allowed.push_back(MsgType_HLTA);
            end
            if (AC) begin
                allowed.push_back(MsgType_AC);
            end
            if (nAC) begin
                allowed.push_back(MsgType_nAC);
            end
            if (SELECT) begin
                allowed.push_back(MsgType_SELECT);
            end
            if (nSELECT) begin
                allowed.push_back(MsgType_nSELECT);
            end
            if (random) begin
                allowed.push_back(MsgType_RANDOM);
            end
            if (error) begin
                allowed.push_back(MsgType_ERROR);
            end

            std::randomize(to_send) with {to_send inside {allowed};};

            // for nAC / nSELECT we allow any level, but make sure the UID doesn't match

            if ((to_send == MsgType_AC) || (to_send == MsgType_SELECT)) begin
                // always use level 0 for AC / SELECT
                // we currently assume the tag is either not in the READY / READY* state
                // or it's in one of those, at level 0
                level       = 0;
            end
            else begin
                // for nAC / nSELECT use whatever level
                level       = $urandom_range(0,2);
            end

            if ((to_send == MsgType_SELECT) || (to_send == MsgType_nSELECT)) begin
                // select messages have 32 bits of UID data
                uid_bits    = 32;
            end
            else if (to_send == MsgType_nAC) begin
                // AC will always match if the level is the correct and uid_bits is 0
                // so don't allow 0 bits or 32 bits.
                uid_bits    = $urandom_range(1,31);
            end
            else begin
                // AC can use any number of bits
                uid_bits    = $urandom_range(32);
            end

            // invent a uid that definitely won't match for MsgType_nAC
            if (uid_bits != 0) begin
                // can't do std::randomize(invalid_uid) with {invalid_uid[uid_bits-1:0] != sel_uid_level[level][uid_bits-1:0];};
                // since that has a variable range
                // so create a wildcard mask, and set the bits we don't care about to ?
                automatic logic [31:0] mask = '0;
                for (int i = 0; i < uid_bits; i++) begin
                    mask[i] = 1'b1;
                end

                std::randomize(invalid_uid) with {(invalid_uid & mask) != (sel_uid_level[level] & mask);};

                //$display("invalid_uid %h for bits %d doesn't match %h, mask %b", invalid_uid, uid_bits, sel_uid_level[level], mask);
            end

            //$display("sending %s", to_send.name);
            case (to_send)
                MsgType_REQA:       return generate_reqa();
                MsgType_WUPA:       return generate_wupa();
                MsgType_HLTA:       return generate_hlta();
                MsgType_AC:         return generate_ac_select (0,     uid_bits, sel_uid_level[0]);
                MsgType_nAC:        return generate_ac_select (level, uid_bits, invalid_uid);
                MsgType_SELECT:     return generate_ac_select (0,     32,       sel_uid_level[0]);
                MsgType_nSELECT:    return generate_ac_select (level, 32,       invalid_uid);
                MsgType_RANDOM:     return generate_random();
                MsgType_ERROR:      return generate_error();
                default:            $fatal(0, "Message %d (%s) not supported here", to_send, to_send.name);
            endcase
        endfunction

        // --------------------------------------------------------------
        // PCD -> PICC send tasks
        // --------------------------------------------------------------

        task send_reqa;
            send_frame(generate_reqa());
        endtask

        task send_wupa;
            send_frame(generate_wupa());
        endtask

        task send_hlta (logic add_crc=1'b1);
            // we have add_crc so we can disable it to mimic a CRC fail
            send_frame(generate_hlta(add_crc));
        endtask

        task send_ac_select (int level, int uid_bits, logic [31:0] uid, logic add_crc_if_select=1'b1, logic flip_last_bit=1'b0);
            send_frame(generate_ac_select(level, uid_bits, uid, add_crc_if_select, flip_last_bit));
        endtask

        task send_random;
            send_frame(generate_random());
        endtask

        task send_error;
            send_frame(generate_error());
        endtask

        task send_msg(logic REQA, logic WUPA, logic HLTA,
                      logic AC, logic nAC, logic SELECT, logic nSELECT,
                      logic random, logic error);
            send_frame(generate_msg(REQA, WUPA, HLTA, AC, nAC, SELECT, nSELECT, random, error));
        endtask

        // --------------------------------------------------------------
        // PICC -> PCD reply validation functions
        // --------------------------------------------------------------

        function logic validate_atqa (MsgFromPICC msg);
            automatic logic [15:0]  expected;
            automatic logic         res;

            case (UID_SIZE)
                UIDSize_SINGLE: expected = 16'h0004;
                UIDSize_DOUBLE: expected = 16'h0044;
                UIDSize_TRIPLE: expected = 16'h0084;
            endcase

            res = (msg.data.size == 2)              &&
                  (msg.bits_in_first_byte == 0)     &&
                  !msg.has_crc                      &&
                  (msg.data[0] == expected[7:0])    &&
                  (msg.data[1] == expected[15:8]);

            atqaAsExpected:
            assert (res) else $error("Failed to receive ATQA as expected: %p", msg);
        endfunction

        function logic validate_ac_reply (MsgFromPICC msg, logic [31:0] uid);
            automatic logic [39:0]  built_uid;
            automatic int           idx;
            automatic int           bits_to_copy;
            automatic logic [7:0]   bcc = uid[31:24] ^ uid[23:16] ^ uid[15:8] ^ uid[7:0];
            automatic logic         res;

            // the AC message constis of 32 UID bits + 8 BCC bits,
            // partially sent by the PCD and partially the PICC
            // copy the part sent by the PCD
            for (idx = 0; idx < last_sent_uid_bits; idx++) built_uid[idx] = uid[idx];

            // only copy bits_in_first_byte of the first byte
            bits_to_copy = msg.bits_in_first_byte;
            if (bits_to_copy == 0) begin
                bits_to_copy = 8;
            end
            foreach (msg.data[i]) begin
                for (int j = 0; j < bits_to_copy; j++) begin
                    built_uid[idx++] = msg.data[i][j];
                end

                // all other bytes must be 8 bits
                bits_to_copy = 8;
            end

            //$display("received AC reply: %p, idx %d, built %h", msg, idx, built_uid);

            res = (idx == 40)               &&
                  !msg.has_crc              &&
                  (uid == built_uid[31:0])  &&
                  (bcc == built_uid[39:32]);

            acReplyAsExpected:
            assert (res) else $error("Failed to receive AC reply as expected: %p, idx %d, built %h", msg, idx, built_uid);
        endfunction

        function logic validate_sak (MsgFromPICC msg, int level);
            automatic       logic       res;
            automatic       logic [7:0] expected;
            automatic const logic [7:0] expectedComplete    = 8'h20;
            automatic const logic [7:0] expectedNotComplete = 8'h04;

            // we won't get any reply at all to a select that's not for our tag's current level
            // so just don't call recv_sak() when not expecting a reply
            if (get_num_sel_levels() == (level+1)) begin
                expected = expectedComplete;
            end
            else begin
                expected = expectedNotComplete;
            end

            res = (msg.data.size == 1)          &&
                  (msg.bits_in_first_byte == 0) &&
                   msg.has_crc                  &&
                  (msg.data[0] == expected[7:0]);

            sakAsExpected:
            assert (res) else $error("Failed to receive SAK as expected, got %p", msg);
        endfunction

        // --------------------------------------------------------------
        // PICC -> PCD receive tasks
        // --------------------------------------------------------------

        task check_no_reply;
            automatic MsgFromPICC msg;
            recv_frame(msg, 1'b1);
            noReply: assert (msg.data.size == 0) else $fatal(1, "Received data when not expecting a reply");
        endtask

        task recv_atqa;
            automatic MsgFromPICC msg;
            recv_frame(msg);
            void'(validate_atqa(msg));
        endtask

        task recv_ac_reply (logic [31:0] uid);
            automatic MsgFromPICC msg;
            recv_frame(msg);
            void'(validate_ac_reply(msg, uid));
        endtask

        task recv_sak (int level);
            automatic MsgFromPICC msg;
            recv_frame(msg);
            void'(validate_sak(msg, level));
        endtask

        // --------------------------------------------------------------
        // Get the DUT into a particular state
        // --------------------------------------------------------------

        task select_tag (logic star);
            automatic int num_sel_levels = get_num_sel_levels();

            // we should be in state READY or READY*

            // Send up to 3 levels of SELECTs
            // and receive the SAK for each level
            for (int level = 0; level < num_sel_levels; level++) begin
                send_frame(generate_ac_select (level, 32, sel_uid_level[level]));

                recv_sak (level);

                if (level + 1 == num_sel_levels) begin
                    // we're done, make sure we've gone active
                    check_state (star ? State_ACTIVE_STAR : State_ACTIVE);
                end
                else begin
                    // not done yet, make sure we're still ready
                    check_state (star ? State_READY_STAR : State_READY);
                end
            end
        endtask

        task go_to_state_idle;
            do_reset;

            check_state(State_IDLE);
        endtask

        task go_to_state_ready;
            go_to_state_idle;

            // we can get to ready by sending REQA or WUPA
            if (1'($urandom)) begin
                send_frame(generate_reqa());
            end
            else begin
                send_frame(generate_wupa());
            end

            // reply to reqa / wupa is ATQA
            recv_atqa;

            check_state(State_READY);
        endtask

        task go_to_state_active;
            go_to_state_ready;
            select_tag(1'b0);

            check_state(State_ACTIVE);
        endtask

        task go_to_state_halt;
            // we can't get to halt from idle or ready
            go_to_state_active;

            // send the HLTA command
            send_frame(generate_hlta());

            // check we don't receive a reply
            check_no_reply;

            check_state(State_HALT);
        endtask

        task go_to_state_ready_star;
            go_to_state_halt;

            // Can't use REQÄ here, has to be WUPa
            send_frame(generate_wupa());

            // reply to wupa is ATQA
            recv_atqa;

            check_state(State_READY_STAR);
        endtask

        task go_to_state_active_star;
            go_to_state_ready_star;
            select_tag(1'b1);

            check_state(State_ACTIVE_STAR);
        endtask

        task go_to_state (State state);
            case (state)
                State_IDLE:         go_to_state_idle;
                State_READY:        go_to_state_ready;
                State_ACTIVE:       go_to_state_active;
                State_HALT:         go_to_state_halt;
                State_READY_STAR:   go_to_state_ready_star;
                State_ACTIVE_STAR:  go_to_state_active_star;
            endcase
        endtask

        // --------------------------------------------------------------------
        // Tests
        // --------------------------------------------------------------------

        task run_all_initialisation_tests;
            // --------------------------------------------------------------------
            // Test all possible state transititions
            // --------------------------------------------------------------------

            // 1) Start in State_IDLE
            //      REQA + WUPA take us to State_READY and reply ATQA
            //      all others leave us in State_IDLE

            // reqa / wupa -> ready + ATQA
            $display("State_IDLE + REQA/WUPA");
            repeat (1000) begin
                go_to_state_idle;
                send_msg(.REQA      (1'b1), .WUPA      (1'b1), .HLTA      (1'b0),
                         .AC        (1'b0), .nAC       (1'b0),
                         .SELECT    (1'b0), .nSELECT   (1'b0),
                         .random    (1'b0), .error     (1'b0));
                recv_atqa;
                check_state(State_READY);
            end

            // all others -> idle + no reply
            $display("State_IDLE + others");
            repeat (1000) begin
                go_to_state_idle;
                send_msg(.REQA      (1'b0), .WUPA      (1'b0),  .HLTA      (1'b1),
                         .AC        (1'b1), .nAC       (1'b1),
                         .SELECT    (1'b1), .nSELECT   (1'b1),
                         .random    (1'b1), .error     (1'b1));
                check_no_reply;
                check_state(State_IDLE);
            end

            // 2) Start in State_READY
            //      AC leaves us in State_READY
            //      SELECT either takes us to State_ACTIVE or leaves us in State_READY depending on level and UID_SIZE
            //      all others return us to State_IDLE

            // AC -> ready + AC reply
            $display("State_READY + AC");
            repeat (1000) begin
                go_to_state_ready;
                // always level 0 for now. We check AC stuff more later
                send_ac_select (0, $urandom_range(31), sel_uid_level[0]);
                recv_ac_reply (sel_uid_level[0]);
                check_state(State_READY);
            end

            // SELECT - just select the tag (as many levels as are needed)
            // we worry about AC / select stuff more later
            $display("State_READY + SELECT");
            repeat (1000) begin
                go_to_state_ready;
                select_tag(1'b0); // this checks the SAKs and state internally
            end

            // all others -> idle, no reply
            $display("State_READY + others");
            repeat (1000) begin
                go_to_state_ready;
                send_msg(.REQA      (1'b1), .WUPA      (1'b1), .HLTA      (1'b1),
                         .AC        (1'b0), .nAC       (1'b1),
                         .SELECT    (1'b0), .nSELECT   (1'b1),
                         .random    (1'b1), .error     (1'b1));
                check_no_reply;
                check_state(State_IDLE);
            end

            // 3) Start in State_ACTIVE
            //      HLTA takes us to State_HALT, no reply
            //      RATS (not supported yet) takes us to State_PROTOCOL + reply
            //      Anything else takes us to State_IDLE, no reply

            // HLTA -> halt, no reply
            $display("State_ACTIVE + HLTA");
            repeat (1000) begin
                go_to_state_active;
                send_hlta();
                check_no_reply;
                check_state(State_HALT);
            end

            // TODO: Checks state transition for RATS

            // all others -> idle, no reply
            $display("State_ACTIVE + others");
            repeat (1000) begin
                go_to_state_active;
                send_msg(.REQA      (1'b1), .WUPA      (1'b1), .HLTA      (1'b0),
                         .AC        (1'b1), .nAC       (1'b1),
                         .SELECT    (1'b1), .nSELECT   (1'b1),
                         .random    (1'b1), .error     (1'b1));
                check_no_reply;
                check_state(State_IDLE);
            end

            // 4) Start in State_HALT
            //      WUPA take us to State_READY_STAR and reply ATQA
            //      all others leave us in State_HALT, no reply

            // wupa -> ready* + ATQA
            $display("State_HALT + WUPA");
            repeat (1000) begin
                go_to_state_halt;
                send_wupa();
                recv_atqa;
                check_state(State_READY_STAR);
            end

            // all others -> idle + no reply
            $display("State_HALT + others");
            repeat (1000) begin
                go_to_state_halt;
                send_msg(.REQA      (1'b1), .WUPA      (1'b0),  .HLTA      (1'b1),
                         .AC        (1'b1), .nAC       (1'b1),
                         .SELECT    (1'b1), .nSELECT   (1'b1),
                         .random    (1'b1), .error     (1'b1));
                check_no_reply;
                check_state(State_HALT);
            end

            // 5) Start in State_READY_STAR
            //      AC leaves us in State_READY_STAR
            //      SELECT either takes us to State_ACTIVE_STAR or leaves us in State_READY_STAR
            //      depending on level and UID_SIZE
            //      all others return us to State_HALT

            // AC -> ready_star + AC reply
            $display("State_READY_STAR + AC");
            repeat (1000) begin
                go_to_state_ready_star;
                // always level 0 for now. We check AC stuff more later
                send_ac_select (0, $urandom_range(31), sel_uid_level[0]);
                recv_ac_reply (sel_uid_level[0]);
                check_state(State_READY_STAR);
            end

            // SELECT - just select the tag (as many levels as are needed)
            // we worry about AC / select stuff more later
            $display("State_READY_STAR + SEL");
            repeat (1000) begin
                go_to_state_ready_star;
                select_tag(1'b1); // this checks the SAKs and state internally
            end

            // all others -> halt, no reply
            $display("State_READY_STAR + others");
            repeat (1000) begin
                go_to_state_ready_star;
                send_msg(.REQA      (1'b1), .WUPA      (1'b1), .HLTA      (1'b1),
                         .AC        (1'b0), .nAC       (1'b1),
                         .SELECT    (1'b0), .nSELECT   (1'b1),
                         .random    (1'b1), .error     (1'b1));
                check_no_reply;
                check_state(State_HALT);
            end

            // 6) Start in State_ACTIVE_STAR
            //      RATS (not supported yet) takes us to State_PROTOCOL + reply
            //      Anything else takes us to State_IDLE, no reply

            // TODO: Checks state transition for RATS

            // all others -> halt, no reply
            $display("State_ACTIVE_STAR + others");
            repeat (1000) begin
                go_to_state_active_star;
                send_msg(.REQA      (1'b1), .WUPA      (1'b1), .HLTA      (1'b1),
                         .AC        (1'b1), .nAC       (1'b1),
                         .SELECT    (1'b1), .nSELECT   (1'b1),
                         .random    (1'b1), .error     (1'b1));
                check_no_reply;
                check_state(State_HALT);
            end

            // TODO: Check transitions from State_PROTOCOL

            // --------------------------------------------------------------------
            // Test AC/SELECT
            // --------------------------------------------------------------------

            begin
                // repeat these tests in both the ready state and the ready* state
                State states [$] = '{State_READY, State_READY_STAR};
                foreach (states[i]) begin

                    // 1) Test all valid ACs for all levels
                    $display("%s + all ACs", states[i].name);
                    for (int level = 0; level < get_num_sel_levels(); level++) begin
                        for (int uid_bits = 0; uid_bits < 32; uid_bits++) begin
                            // go to the ready/ready* state
                            go_to_state(states[i]);

                            // send previous selects
                            for (int l = 0; l < level; l++) begin
                                send_ac_select (l, 32, sel_uid_level[l]);
                                recv_sak (l);

                                // confirm we're still in states[i]
                                check_state(states[i]);
                            end

                            // send AC with uid_bits
                            send_ac_select (level, uid_bits, sel_uid_level[level]);
                            recv_ac_reply (sel_uid_level[level]);

                            // confirm we're still in states[i]
                            check_state(states[i]);
                        end
                    end

                    // 2) Test invalid nACs / nSELECTs with the tag in all levels
                    //    we've already tested this with the tag in level 0, but repeat anyway
                    $display("%s + nAC/nSELECT", states[i].name);
                    for (int level = 0; level < get_num_sel_levels(); level++) begin
                        repeat (1000) begin
                            // go to the ready/ready* state
                            go_to_state(states[i]);

                            // send previous selects
                            for (int l = 0; l < level; l++) begin
                                send_ac_select (l, 32, sel_uid_level[l]);
                                recv_sak (l);

                                // confirm we're still in states[i]
                                check_state(states[i]);
                            end

                            // send nAC / nSELECT
                            send_msg(.REQA      (1'b0), .WUPA      (1'b0), .HLTA      (1'b0),
                                     .AC        (1'b0), .nAC       (1'b1),
                                     .SELECT    (1'b0), .nSELECT   (1'b1),
                                     .random    (1'b0), .error     (1'b0));
                            check_no_reply;

                            // confirm we're in IDLE / HALT
                            check_state((states[i] == State_READY) ? State_IDLE : State_HALT);
                        end
                    end

                    // 3) test all valid ACs / SELECTs but for the wrong level
                    $display("%s + AC/SELECT for wrong level", states[i].name);
                    for (int actualLevel = 0; actualLevel < get_num_sel_levels(); actualLevel++) begin
                        for (int sendLevel = 0; sendLevel < 3; sendLevel++) begin
                            // don't send correct ACs
                            if (sendLevel == actualLevel) begin
                                continue;
                            end

                            for (int uid_bits = 0; uid_bits <= 32; uid_bits++) begin
                                // go to the ready/ready* state
                                go_to_state(states[i]);

                                // send previous selects
                                for (int l = 0; l < actualLevel; l++) begin
                                    send_ac_select (l, 32, sel_uid_level[l]);
                                    recv_sak (l);

                                    // confirm we're still in states[i]
                                    check_state(states[i]);
                                end

                                // send AC with uid_bits
                                send_ac_select (sendLevel, uid_bits, sel_uid_level[sendLevel]);
                                check_no_reply;

                                // confirm we're in IDLE / HALT
                                check_state((states[i] == State_READY) ? State_IDLE : State_HALT);
                            end
                        end
                    end

                    // 4) send the correct AC/SELECT for this level, but with the level code incorrect
                    $display("%s + AC/SELECT with level code incorrect", states[i].name);
                    for (int actualLevel = 0; actualLevel < get_num_sel_levels(); actualLevel++) begin
                        for (int sendLevel = 0; sendLevel < 3; sendLevel++) begin
                            // don't send correct ACs
                            if (sendLevel == actualLevel) begin
                                continue;
                            end

                            // start with uid_bits == 1, otherwise it's always valid
                            for (int uid_bits = 1; uid_bits <= 32; uid_bits++) begin
                                // go to the ready/ready* state
                                go_to_state(states[i]);

                                // send previous selects
                                for (int l = 0; l < actualLevel; l++) begin
                                    send_ac_select (l, 32, sel_uid_level[l]);
                                    recv_sak (l);

                                    // confirm we're still in states[i]
                                    check_state(states[i]);
                                end

                                // send AC with uid_bits, correct data but wrong level
                                send_ac_select (sendLevel, uid_bits, sel_uid_level[actualLevel]);
                                check_no_reply;

                                // confirm we're in IDLE / HALT
                                check_state((states[i] == State_READY) ? State_IDLE : State_HALT);
                            end
                        end
                    end

                    // 5) send SELECT with the last bit wrong.
                    //    this makes sure that UID Matching runs for the entire UID
                    $display("%s + SELECT with last bit wrong", states[i].name);
                    for (int level = 0; level < get_num_sel_levels(); level++) begin
                        // go to the ready/ready* state
                        go_to_state(states[i]);

                        // send previous selects
                        for (int l = 0; l < level; l++) begin
                            send_ac_select (l, 32, sel_uid_level[l]);
                            recv_sak (l);

                            // confirm we're still in states[i]
                            check_state(states[i]);
                        end

                        // send SELECT, flipping the last bit
                        // IE. not for us
                        send_ac_select (level, 32, sel_uid_level[level], 1'b1, 1'b1);

                        check_no_reply;

                        // confirm we're in IDLE / HALT
                        check_state((states[i] == State_READY) ? State_IDLE : State_HALT);
                    end
                end
            end

            // --------------------------------------------------------------------
            // Test CRC errors
            // --------------------------------------------------------------------
            // only two messages use CRCs, HLTA and SELECT
            // CRC fail is counted as a transmission error and should return us to HALT / IDLE

            $display("Testing SELECT with CRC error");
            repeat (10) begin
                // SELECT is only valid in State_READY or State_READY_STAR
                automatic State states [$] = '{State_READY, State_READY_STAR};
                automatic State start_state;

                std::randomize(start_state) with {start_state inside {states};};
                go_to_state(start_state);

                // valid select but without the CRC
                send_ac_select (0, 32, sel_uid_level[0], 1'b0);

                check_no_reply;

                // confirm we're in IDLE / HALT
                check_state((start_state == State_READY) ? State_IDLE : State_HALT);
            end

            $display("Testing HLTA with CRC error");
            repeat (100) begin
                // HLTA can be sent from any state other than PROTOCOL
                // (although in READY and IDLE we go to IDLE)
                // It's a bit silly that HLTA requires a CRC.
                // Since it does not respond in either case and
                // CRC fail counts as an error, which always does the same
                // as what a valid HLTA would have done in that case.
                // except in State_ACTIVE where we return to IDLE for an error
                // and go to HALT with a valid HLTA.
                automatic State states [$] = '{State_IDLE, State_READY,      State_ACTIVE,
                                               State_HALT, State_READY_STAR, State_ACTIVE_STAR};
                automatic State start_state;

                std::randomize(start_state) with {start_state inside {states};};
                go_to_state(start_state);
                //$display("starting in state %s", start_state.name);

                // valid select but without the CRC
                send_hlta(1'b0);

                check_no_reply;

                // confirm we're in IDLE / HALT
                check_state(((start_state == State_IDLE) ||
                             (start_state == State_READY) ||
                             (start_state == State_ACTIVE)) ? State_IDLE : State_HALT);
            end

        endtask

    endclass

endpackage
