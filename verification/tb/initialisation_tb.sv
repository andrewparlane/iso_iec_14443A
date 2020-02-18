/***********************************************************************
        File: initialisation_tb.sv
 Description: Testbench for the initialisation module
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

module initialisation_tb
#(
    // can't work out how to change enum parameters via command line arguments
    // use integers instead
    // 0 -> UIDSize_SINGLE, 1 -> UIDSize_DOUBLE, others -> UIDSize_TRIPLE
    parameter int                           UID_SIZE_CODE   = 0,

    // How many UID bits are variable (via the uid input port)?
    // defaults such that UID_FIXED has 2 bits
    parameter int                           UID_INPUT_BITS  = ISO14443A_pkg::get_uid_bits(get_uid_size()) - 2,

    // don't overwrite this
    parameter int                           UID_FIXED_BITS  = ISO14443A_pkg::get_uid_bits(get_uid_size()) -
                                                              UID_INPUT_BITS,

    // The fixed bits of the UID (defaults to 0)
    parameter logic [UID_FIXED_BITS-1:0]    UID_FIXED       = '0
);

    import ISO14443A_pkg::*;

    // --------------------------------------------------------------
    // Parameters
    // --------------------------------------------------------------

    // function so we can use UID_SIZE in the parameter list
    function UIDSize get_uid_size;
        return (UID_SIZE_CODE == 0) ? UIDSize_SINGLE :
               (UID_SIZE_CODE == 1) ? UIDSize_DOUBLE :
                                      UIDSize_TRIPLE;
    endfunction

    // Are we using single, double or triple UIDs
    localparam UIDSize UID_SIZE = get_uid_size();

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic                       clk;
    logic                       rst_n;

    // The variable part of the UID
    // should come from flash or dip switches / wire bonding / hardcoded
    // I assume this is constant in my code. So I'd recommend only changing it
    // while this IP core is in reset. That may not be strictly necesarry, but
    // further investigation would be necesarry to be sure.
    logic [UID_INPUT_BITS-1:0]  uid_variable;

    // Receive signals
    logic                       rx_soc;
    logic                       rx_eoc;
    logic [7:0]                 rx_data;
    logic [2:0]                 rx_data_bits;
    logic                       rx_data_valid;
    logic                       rx_error;
    logic                       rx_crc_ok;

    // From the iso14443-4 block
    // tells us if a deselect command has been received
    logic                       iso14443_4_deselect;

    // Transmit signals
    logic                       tx_req;
    logic [7:0]                 tx_data;
    logic [2:0]                 tx_data_bits;
    logic                       tx_ready_to_send;
    logic                       tx_append_crc;

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    initialisation
    #(
        .UID_SIZE       (UID_SIZE),
        .UID_INPUT_BITS (UID_INPUT_BITS),
        .UID_FIXED      (UID_FIXED)
    )
    dut (.*);

    // --------------------------------------------------------------
    // UID
    // --------------------------------------------------------------

    // Our entire UID is based on the fixed part passed as a parameter
    // and the variable part passed to the input port.
    // we make this 10 bytes wide for triple UIDs, even if we don't use UIDSize_TRIPLE
    // so that our randomisation can work easier
    logic [79:0] tag_uid;

    // the UIDs to send in the SELECT / AC command including the cascade tags
    logic [31:0] sel_uid_level [3];

    generate
        if (UID_SIZE == UIDSize_SINGLE) begin: uidSingle
            assign tag_uid = {48'b0, UID_FIXED, uid_variable};
            assign sel_uid_level[0] = tag_uid[31:0];
            assign sel_uid_level[1] = '0;
            assign sel_uid_level[2] = '0;
        end
        else if (UID_SIZE == UIDSize_DOUBLE) begin: uidDouble
            assign tag_uid = {24'b0, UID_FIXED, uid_variable};
            assign sel_uid_level[0] = {tag_uid[23:0], 8'h88};
            assign sel_uid_level[1] = tag_uid[55:24];
            assign sel_uid_level[2] = '0;
        end
        else begin: uidTriple
            assign tag_uid = {UID_FIXED, uid_variable};
            assign sel_uid_level[0] = {tag_uid[23:0],  8'h88};
            assign sel_uid_level[1] = {tag_uid[47:24], 8'h88};
            assign sel_uid_level[2] = tag_uid[79:48];
        end
    endgenerate

    // --------------------------------------------------------------
    // PICC -> PCD clock and comms generator
    // --------------------------------------------------------------
    // just used for generating the clk and calculating CRCs
    iso14443a_pcd_to_picc_comms_generator bfm
    (
        .clk            (clk),
        .pcd_pause_n    (),
        .pause_n        (),
        .sending        ()
    );

    // --------------------------------------------------------------
    // Functions / Tasks
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
        Msg_REQA,
        Msg_WUPA,
        Msg_HLTA,
        Msg_AC,
        Msg_nAC,
        Msg_SELECT,
        Msg_nSELECT,
        Msg_RANDOM,
        Msg_ERROR
    } Msg;

    function int get_num_sel_levels;
        case (UID_SIZE)
            UIDSize_SINGLE: return 1;
            UIDSize_DOUBLE: return 2;
            UIDSize_TRIPLE: return 3;
            default: $fatal("invalid UID_SIZE");
        endcase
    endfunction

    task send_frame (logic [7:0] dq[$], int bits_in_last_byte, logic add_crc, int error_in_byte = -1);
        automatic logic [15:0] crc = bfm.calculate_crc(dq);
        automatic int loopLimit;
        automatic int i;
        automatic bit sent_error = 1'b0;

        if (bits_in_last_byte == 0) begin
            bits_in_last_byte = 8;
        end

        if (add_crc) begin
            dq.push_back(crc[7:0]);
            dq.push_back(crc[15:8]);
        end

        rx_soc          <= 1'b0;
        rx_eoc          <= 1'b0;
        rx_data_bits    <= '0;      // 8 bits
        rx_data_valid   <= 1'b0;
        rx_error        <= 1'b0;
        rx_crc_ok       <= 1'b0;

        // sync to clock
        @(posedge clk) begin end

        // SOC
        rx_soc <= 1'b1;
        @(posedge clk) begin end
        rx_soc <= 1'b0;
        @(posedge clk) begin end

        // DATA
        loopLimit = dq.size;
        if (bits_in_last_byte != 8) begin
            loopLimit--;
        end
        for (i = 0; i < loopLimit; i++) begin
            rx_data         <= dq[i];
            if (error_in_byte == i) begin
                rx_error        <= 1'b1;
                sent_error      = 1'b1;
            end
            else if (!sent_error) begin
                rx_data_valid   <= 1'b1;
            end
            @(posedge clk) begin end
            rx_error        <= 1'b0;
            rx_data_valid   <= 1'b0;
            @(posedge clk) begin end
        end

        // partial byte
        if (bits_in_last_byte != 8) begin
            rx_data         <= dq[$];
            if (error_in_byte == i) begin
                rx_error        <= 1'b1;
                sent_error       = 1'b1;
            end
            else if (!sent_error) begin
                rx_data_valid   <= 1'b1;
            end
            rx_data_bits    <= 3'(bits_in_last_byte);
        end

        // EOC
        rx_eoc              <= 1'b1;
        @(posedge clk) begin end
        rx_eoc              <= 1'b0;
        rx_data_valid       <= 1'b0;
        rx_error            <= 1'b0;

        // CRC
        if (add_crc && !sent_error) begin
            rx_crc_ok       <= 1'b1;
            @(posedge clk) begin end
            rx_crc_ok       <= 1'b0;
        end
    endtask

    task send_reqa;
        send_frame ('{8'h26}, 7, 0);
    endtask

    task send_wupa;
        send_frame ('{8'h52}, 7, 0);
    endtask

    task send_hlta;
        send_frame ('{8'h50, 8'h00}, 8, 1);
    endtask

    int last_sent_uid_bits;
    task send_ac_select (int level, int uid_bits, logic [31:0] uid);
        // the AC/SELECT message is: sel, nvb, uid0, uid1, uid2, uid3, bcc

        automatic logic [7:0]   dq[$];
        automatic int           bytes_to_send       = 2 + $rtoi(real'(uid_bits) / 8.0); // $rtoi for truncate not round
        automatic int           bits_in_last_byte   = uid_bits % 8;
        automatic logic [7:0]   bcc                 = uid[31:24] ^ uid[23:16] ^ uid[15:8] ^ uid[7:0];

        // cache the number of sent bits for the AC reply
        last_sent_uid_bits = uid_bits;

        if (uid_bits == 32) begin
            // send all of the UID so add BCC
            bytes_to_send++;
        end

        dq.delete;

        // SEL
        case (level)
            0: dq.push_back(8'h93);
            1: dq.push_back(8'h95);
            2: dq.push_back(8'h97);
            default: $error("Invalsid level %d passed to send_ac_select", level);
        endcase

        // NVB
        dq.push_back({4'(bytes_to_send), 4'(bits_in_last_byte)});

        // UID
        for (int i = uid_bits; i > 0; i-=8) begin
            dq.push_back(uid[7:0]);
            uid = {8'h0, uid[31:8]};
        end

        // BCC
        if (uid_bits == 32) begin
            dq.push_back(bcc);
        end

        // send it
        //$display("sending AC/SELECT %p, bits_in_last_byte %d, add_crc %b", dq, bits_in_last_byte, (uid_bits == 32));
        send_frame (dq, bits_in_last_byte, (uid_bits == 32));
    endtask

    task send_random;
        automatic int bytes_to_send     = $urandom_range(1, 20);
        automatic int bits_in_last_byte = $urandom_range(0, 7);
        automatic logic [7:0] dq [$];

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

            dq.push_back(b);
        end

        //$display("sending random msg: %p, bits_in_last_byte %d", dq, bits_in_last_byte);

        send_frame(dq, bits_in_last_byte, 1'($urandom));
    endtask

    task send_error;
        automatic int bytes_to_send     = $urandom_range(1, 20);
        automatic int bits_in_last_byte = $urandom_range(0, 7);
        automatic int error_in_byte     = $urandom_range(0, bytes_to_send - 1);
        automatic logic [7:0] dq [$];

        for (int i = 0; i < bytes_to_send; i++) begin
            automatic logic [7:0] b;
            std::randomize(b);
            dq.push_back(b);
        end

        send_frame(dq, bits_in_last_byte, 1'($urandom), error_in_byte);
    endtask

    task send_msg(logic REQA, logic WUPA, logic HLTA,
                  logic AC, logic nAC, logic SELECT, logic nSELECT,
                  logic random, logic error);
        automatic Msg           allowed [$] = '{};
        automatic Msg           to_send;
        automatic int           level;
        automatic int           uid_bits;
        automatic logic [31:0]  invalid_uid;

        if (REQA) begin
            allowed.push_back(Msg_REQA);
        end
        if (WUPA) begin
            allowed.push_back(Msg_WUPA);
        end
        if (HLTA) begin
            allowed.push_back(Msg_HLTA);
        end
        if (AC) begin
            allowed.push_back(Msg_AC);
        end
        if (nAC) begin
            allowed.push_back(Msg_nAC);
        end
        if (SELECT) begin
            allowed.push_back(Msg_SELECT);
        end
        if (nSELECT) begin
            allowed.push_back(Msg_nSELECT);
        end
        if (random) begin
            allowed.push_back(Msg_RANDOM);
        end
        if (error) begin
            allowed.push_back(Msg_ERROR);
        end

        std::randomize(to_send) with {to_send inside {allowed};};

        // for nAC / nSELECT we allow any level, but make sure the UID doesn't match

        if ((to_send == Msg_AC) || (to_send == Msg_SELECT)) begin
            // always use level 0 for AC / SELECT
            // we currently assume the tag is either not in the READY / READY* state
            // or it's in one of those, at level 0
            level       = 0;
        end
        else begin
            // for nAC / nSELECT use whatever level
            level       = $urandom_range(0,2);
        end

        if ((to_send == Msg_SELECT) || (to_send == Msg_nSELECT)) begin
            // select messages have 32 bits of UID data
            uid_bits    = 32;
        end
        else if (to_send == Msg_nAC) begin
            // AC will always match if the level is the correct and uid_bits is 0
            // so don't allow 0 bits or 32 bits.
            uid_bits    = $urandom_range(1,31);
        end
        else begin
            // AC can use any number of bits
            uid_bits    = $urandom_range(32);
        end

        // invent a uid that definitely won't match for Msg_nAC
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
            Msg_REQA:       send_reqa;
            Msg_WUPA:       send_wupa;
            Msg_HLTA:       send_hlta;
            Msg_AC:         send_ac_select (0,     uid_bits, sel_uid_level[0]);
            Msg_nAC:        send_ac_select (level, uid_bits, invalid_uid);
            Msg_SELECT:     send_ac_select (0,     32,       sel_uid_level[0]);
            Msg_nSELECT:    send_ac_select (level, 32,       invalid_uid);
            Msg_RANDOM:     send_random;
            Msg_ERROR:      send_error;
        endcase
    endtask

    task recv_data (output logic [7:0] dq[$], output int bits_in_first_byte, output logic crc);
        tx_req <= 1'b0;

        // wait 32 ticks, data should be ready by then
        // in the real world it has ~1100 ticks (for the FDT) but we don't need to wait that long
        repeat (32) @(posedge clk) begin end

        dq.delete;
        while (tx_ready_to_send) begin: txRTSLoop
            dq.push_back(tx_data);

            // we should only have tx_data_bits != 0 on the first byte
            if (dq.size == 1) begin
                bits_in_first_byte = (tx_data_bits == 0) ? 8 : tx_data_bits;
            end
            else begin: notFirstByte
                txFullByte: assert (tx_data_bits == 0)
                            else $error("tx_data_bits (%d) != 0 on byte %d", tx_data_bits, dq.size());
            end

            // request more data
            tx_req <= 1'b1;
            @(posedge clk) begin end
            tx_req <= 1'b0;
            @(posedge clk) begin end
        end
        crc = tx_append_crc;
    endtask

    task recv_atqa;
        automatic logic [15:0]  expected;
        automatic logic [7:0]   dq[$];
        automatic int           bits_in_first_byte;
        automatic logic         crc;

        case (UID_SIZE)
            UIDSize_SINGLE: expected = 16'h0004;
            UIDSize_DOUBLE: expected = 16'h0044;
            UIDSize_TRIPLE: expected = 16'h0084;
        endcase

        recv_data (dq, bits_in_first_byte, crc);

        atqaAsExpected:
        assert ((dq.size == 2)              &&
                (bits_in_first_byte == 8)   &&
                !crc                        &&
                (dq[0] == expected[7:0])    &&
                (dq[1] == expected[15:8]))
            else $error("Failed to receive ATQA as expected");
    endtask

    task check_no_reply;
        automatic logic [7:0]   dq[$];
        automatic int           bits_in_first_byte;
        automatic logic         crc;

        recv_data (dq, bits_in_first_byte, crc);

        noReply: assert (dq.size == 0) else $fatal(1, "Received data when not expecting a reply");
    endtask

    task recv_ac_reply (logic [31:0] uid);
        automatic logic [39:0]  built_uid;
        automatic int           bits_to_copy;
        automatic int           idx;
        automatic logic [7:0]   bcc = uid[31:24] ^ uid[23:16] ^ uid[15:8] ^ uid[7:0];

        automatic logic [7:0]   dq[$];
        automatic int           bits_in_first_byte;
        automatic logic         crc;

        // the AC message constis of 32 UID bits + 8 BCC bits,
        // partially sent by the PCD and partially the PICC
        // copy the part sent by the PCD
        for (idx = 0; idx < last_sent_uid_bits; idx++) built_uid[idx] = uid[idx];

        recv_data (dq, bits_in_first_byte, crc);

        // only copy bits_in_first_byte of the first byte
        bits_to_copy = bits_in_first_byte;
        foreach (dq[i]) begin
            for (int j = 0; j < bits_to_copy; j++) begin
                built_uid[idx++] = dq[i][j];
            end

            // all other bytes must be 8 bits
            bits_to_copy = 8;
        end

        //$display("received AC reply: %p, bits_in_first_byte %d, idx %d, build %h", dq, bits_in_first_byte, idx, built_uid);

        acReplyAsExpected:
        assert ((idx == 40)                 &&
                !crc                        &&
                (uid == built_uid[31:0])    &&
                (bcc == built_uid[39:32]))
            else $error("Failed to receive AC reply as expected");
    endtask

    task recv_sak (int level);
        automatic logic [7:0]   expected;
        automatic logic [7:0]   dq[$];
        automatic int           bits_in_first_byte;
        automatic logic         crc;

        automatic const logic [7:0] expectedComplete    = 8'h20;
        automatic const logic [7:0] expectedNotComplete = 8'h04;

        // we won't get any reply at all to a select that's not for our tag's current level
        // so just don't call recv_sak() when not expecting a reply
        if (get_num_sel_levels() == (level+1)) begin
            expected    = expectedComplete;
        end
        else begin
            expected    = expectedNotComplete;
        end

        recv_data (dq, bits_in_first_byte, crc);

        sakAsExpected:
        assert ((dq.size == 1)              &&
                (bits_in_first_byte == 8)   &&
                crc                         &&
                (dq[0] == expected[7:0]))
            else $error("Failed to receive SAK as expected, got %p, bits_in_first_byte %d, crc %d", dq, bits_in_first_byte, crc);
    endtask

    task select_tag (logic star);
        automatic int num_sel_levels = get_num_sel_levels();

        // we should be in state READY or READY*

        // Send up to 3 levels of SELECTs
        // and receive the SAK for each level
        for (int level = 0; level < num_sel_levels; level++) begin
            send_ac_select (level, 32, sel_uid_level[level]);

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
        rst_n <= 1'b0;
        @(posedge clk) begin end
        rst_n <= 1'b1;
        @(posedge clk) begin end

        check_state(State_IDLE);
    endtask

    task go_to_state_ready;
        go_to_state_idle;

        // we can get to ready by sending REQA or WUPA
        if (1'($urandom)) begin
            send_reqa;
        end
        else begin
            send_wupa;
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
        send_hlta;

        // check we don't receive a reply
        check_no_reply;

        check_state(State_HALT);
    endtask

    task go_to_state_ready_star;
        go_to_state_halt;

        // Can't use REQÄ here, has to be WUPa
        send_wupa;

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
            State_IDLE:          go_to_state_idle;
            State_READY:         go_to_state_ready;
            State_ACTIVE:        go_to_state_active;
            State_HALT:          go_to_state_halt;
            State_READY_STAR:    go_to_state_ready_star;
            State_ACTIVE_STAR:   go_to_state_active_star;
        endcase
    endtask

    function void check_state (State state);
        case (state)
            State_IDLE:          isIdle:        assert ((dut.state == dut.State_IDLE)   && !dut.state_star) else $error("DUT not in correct state expected State_IDLE, 0 got %s, %b", dut.state.name, dut.state_star);
            State_READY:         isReady:       assert ((dut.state == dut.State_READY)  && !dut.state_star) else $error("DUT not in correct state expected State_READY, 0 got %s, %b", dut.state.name, dut.state_star);
            State_ACTIVE:        isActive:      assert ((dut.state == dut.State_ACTIVE) && !dut.state_star) else $error("DUT not in correct state expected State_ACTIVE, 0 got %s, %b", dut.state.name, dut.state_star);
            State_HALT:          isHalt:        assert ((dut.state == dut.State_IDLE)   && dut.state_star)  else $error("DUT not in correct state expected State_IDLE, 1 got %s, %b", dut.state.name, dut.state_star);
            State_READY_STAR:    isReadyStar:   assert ((dut.state == dut.State_READY)  && dut.state_star)  else $error("DUT not in correct state expected State_READY, 1 got %s, %b", dut.state.name, dut.state_star);
            State_ACTIVE_STAR:   isActiveStar:  assert ((dut.state == dut.State_ACTIVE) && dut.state_star)  else $error("DUT not in correct state expected State_ACTIVE, 1 got %s, %b", dut.state.name, dut.state_star);
        endcase
    endfunction

    task randomise_uid;
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
    endtask

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin
        rx_soc                  <= 1'b0;
        rx_eoc                  <= 1'b0;
        rx_data_valid           <= 1'b0;
        rx_error                <= 1'b0;
        iso14443_4_deselect     <= 1'b0;
        tx_req                  <= 1'b0;

        last_sent_uid_bits      <= '0;

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // repeat 100 times with different UIDs
        repeat (100) begin
            // TODO: Add a parameter to let me instead test all possible variable_uid values
            //       For when running initialisation_tb_actual with UID_INPUT_BITS being small

            // randomise the variable part of the UID
            randomise_uid;
            $display("UID_SIZE: %s, UID_INPUT_BITS: %d, UID_FIXED: 'b%b, Our UID: %h",
                     UID_SIZE.name, UID_INPUT_BITS, UID_FIXED, tag_uid);

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
                send_hlta;
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
                send_wupa;
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
                end
            end
        end

        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

    // tx_ready_to_send can only deassetr after tx_req
    rtsDeassertsAfterReq:
    assert property (
        @(posedge clk)
        $fell(tx_ready_to_send) |-> $fell(tx_req))
        else $error("Tx RTS fell while tx_req was stable");

    // once tx_ready_to_send deasserts it can't reassert until after an EOC
    rtsStaysLowUntilNextEOC:
    assert property (
        @(posedge clk)
        $fell(tx_ready_to_send) |=> !tx_ready_to_send throughout rx_eoc[->1])
        else $error("Tx RTS asserted when not expected");

    // rts should be low during Rx
    rtsStaysLowDuringRx:
    assert property (
        @(posedge clk)
        $rose(rx_soc) |=> !tx_ready_to_send throughout rx_eoc[->1])
        else $error("Tx RTS asserted during Rx");

endmodule
