/***********************************************************************
        File: initialisation.sv
 Description: Receives and Replies to ISO 14443-3 init and AC messages
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

module initialisation
#(
    // Are we using single, double or triple UIDs
    parameter ISO14443A_pkg::UIDSize                                            UID_SIZE,

    // How many UID bits are variable (via the uid input port)?
    // must be > 0 and <= the total number of bits in the UID
    // If you want a fixed UID then you can just set this to 1 and hardcode
    // uid[0] to whatever you want.
    parameter int                                                               UID_INPUT_BITS,

    // The fixed bits of the UID
    // the final UID is {UID_FIXED, uid_variable}
    parameter logic [ISO14443A_pkg::get_uid_bits(UID_SIZE)-1:UID_INPUT_BITS]    UID_FIXED
)
(
    // clk is our 13.56MHz input clock. It is recovered from the carrier wave,
    // and as such stops during pause frames. It must not have any glitches.
    input                       clk,

    // rst is our active low synchronised asynchronous reset signal
    input                       rst_n,

    // The variable part of the UID
    // should come from flash or dip switches / wire bonding / hardcoded
    // I assume this is constant in my code. So I'd recommend only changing it
    // while this IP core is in reset. That may not be strictly necesarry, but
    // further investigation would be necesarry to be sure.
    input [UID_INPUT_BITS-1:0]  uid_variable,

    // Receive signals
    input                       rx_soc,
    input                       rx_eoc,
    input           [7:0]       rx_data,
    input           [2:0]       rx_data_bits,
    input                       rx_data_valid,
    input                       rx_error,
    input                       rx_crc_ok,

    // From the iso14443-4 block
    // tells us if a deselect command has been received
    input                       iso14443_4_deselect,

    // Transmit signals
    input                       tx_req,
    output logic    [7:0]       tx_data,
    output logic    [2:0]       tx_data_bits,
    output logic                tx_ready_to_send,
    output logic                tx_append_crc
);

    import ISO14443A_pkg::*;

    // ========================================================================
    // Set up the UID data
    // ========================================================================

    // Our entire UID is based on the fixed part passed as a parameter
    // and the variable part passed to the input port
    logic [get_uid_bits(UID_SIZE)-1:0] uid;
    assign uid = {UID_FIXED, uid_variable};

    // cascade levels 0,1,2
    logic [1:0] current_cascade_level;
    logic [1:0] next_cascade_level;

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            current_cascade_level   <= '0;
        end
        else begin
            current_cascade_level   <= next_cascade_level;
        end
    end

    // are we in the final cascade level?
    logic is_final_cascade_level;

    // the SELECT code, used to make sure the AC/SELECT message has the right level for us
    logic [7:0] current_cascade_level_code;
    assign current_cascade_level_code = (current_cascade_level == 0) ? SEL1 :
                                        (current_cascade_level == 1) ? SEL2 :
                                                                       SEL3;

    // put the expected data for the current cascade level here
    UIDData current_cascade_uid_data;

    // Our our expected UID for each cascade level
    // see ISO/IEC 14443-3:2016 Section 6.5.4
    generate
        if (UID_SIZE == UIDSize_SINGLE) begin: uidSingle
            // For single UIDs there's only the first cascade level
            // and it contains all of the UID
            logic [31:0] uid_cascade_1;

            assign uid_cascade_1                = uid[31:0];
            assign current_cascade_uid_data.uid = uid_cascade_1;
            assign is_final_cascade_level       = 1'b1;
        end
        else begin: notUidSingle
            // for double and triple UIDs the first cascade level has the CASCADE_TAG
            // and then the lower 24 bits of the UID
            logic [31:0] uid_cascade_1;
            assign uid_cascade_1                    = {uid[23:0], CASCADE_TAG};

            if (UID_SIZE == UIDSize_DOUBLE) begin: uidDouble
                // For double UIDs there are two cascade levels
                // the second has the upper 4 bytes of the UID
                logic [31:0] uid_cascade_2;

                assign uid_cascade_2                = uid[55:24];
                assign current_cascade_uid_data.uid = (current_cascade_level == 0) ? uid_cascade_1 :
                                                                                     uid_cascade_2;
                assign is_final_cascade_level       = (current_cascade_level == 1);
            end
            else if (UID_SIZE == UIDSize_TRIPLE) begin: uidTriple
                // For tripel UIDs there are three cascade levels
                // the second has the middle 3 bytes of the UID and the CASCADE_TAG
                // the third has the upper 4 bytes of the UID
                logic [31:0] uid_cascade_2;
                logic [31:0] uid_cascade_3;

                assign uid_cascade_2                = {uid[47:24], CASCADE_TAG};
                assign uid_cascade_3                = uid[79:48];
                assign current_cascade_uid_data.uid = (current_cascade_level == 0) ? uid_cascade_1 :
                                                      (current_cascade_level == 1) ? uid_cascade_2 :
                                                                                     uid_cascade_3;
                assign is_final_cascade_level       = (current_cascade_level == 2);
            end
            else begin
                // cause a synth error
                synth_time_error uid_size_invalid(.*);
            end
        end
    endgenerate

    // calculate the BCC for the current cascade level
    assign current_cascade_uid_data.bcc = current_cascade_uid_data.uid[31:24] ^
                                          current_cascade_uid_data.uid[23:16] ^
                                          current_cascade_uid_data.uid[15: 8] ^
                                          current_cascade_uid_data.uid[7 : 0];

    // ========================================================================
    // Clock in the Rx message and detect errors
    // ========================================================================

    // The largest message we could receive is the SELECT message
    // consisting of 7 bytes (+ 2 bytes of CRC, which we drop since we check it in the parent module)
    localparam int RX_BUFF_LEN = 7;
    logic [7:0] rx_buffer [RX_BUFF_LEN];
    logic [2:0] rx_count;
    logic       rx_error_flag;
    logic       pkt_received;
    logic       is_AC_SELECT_for_us;      // check if it's for us or not

    // compare the received byte with the correct byte of the uid data
    // there may be a better way to do this? Potentially rewriting the rx module
    // to provide bit at a time instead of byte at a time.
    // TODO: Is it worth doing this?
    // another option is to just compare whole bytes, and then
    // after the EOC shift the data bit by bit and check them over a few clock cycles
    logic rx_matches_uid_data_byte;
    always_comb begin
        logic [7:0] uid_data_byte;
        case (rx_count)
            //0: level
            //1: NVB
            2:          uid_data_byte = current_cascade_uid_data.uid[7:0];
            3:          uid_data_byte = current_cascade_uid_data.uid[15: 8];
            4:          uid_data_byte = current_cascade_uid_data.uid[23:16];
            5:          uid_data_byte = current_cascade_uid_data.uid[31:24];
            default:    uid_data_byte = current_cascade_uid_data.bcc;
        endcase

        // now compare it with the received data (depending on how many bits we received)
        case (rx_data_bits)
            1: rx_matches_uid_data_byte = (uid_data_byte[0:0] == rx_data[0:0]);
            2: rx_matches_uid_data_byte = (uid_data_byte[1:0] == rx_data[1:0]);
            3: rx_matches_uid_data_byte = (uid_data_byte[2:0] == rx_data[2:0]);
            4: rx_matches_uid_data_byte = (uid_data_byte[3:0] == rx_data[3:0]);
            5: rx_matches_uid_data_byte = (uid_data_byte[4:0] == rx_data[4:0]);
            6: rx_matches_uid_data_byte = (uid_data_byte[5:0] == rx_data[5:0]);
            7: rx_matches_uid_data_byte = (uid_data_byte[6:0] == rx_data[6:0]);
            0: rx_matches_uid_data_byte = (uid_data_byte[7:0] == rx_data[7:0]);
        endcase
    end

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            rx_count                <= '0;
            rx_error_flag           <= 1'b0;
            pkt_received            <= 1'b0;
        end
        else begin
            // this should only assert for one tick at a time
            pkt_received    <= 1'b0;

            // I don't check that these signals are correct. There are various things
            // that would cause trouble here such as rx_data_bits != 0 when rx_eoc == 0
            // But we have to assume that the rx module produces valid signals, and that
            // the Rx testbench will catch any problems.

            if (rx_soc) begin
                // start of a new message
                rx_count            <= '0;
                rx_error_flag       <= 1'b0;

                // assume that if it's a AC / select message then it's for us
                // we'll set this to 0 later if it doesn't match
                is_AC_SELECT_for_us <= 1'b1;
            end

            if (rx_eoc) begin
                // we use this rather than rx_eoc directly,
                // because for partial packets the rx_data_valid assserts
                // at the same time, and so our rx_buffer won't be correct
                // until the next tick.
                pkt_received    <= 1'b1;
            end

            if (rx_error) begin
                rx_error_flag   <= 1'b1;
            end

            if (rx_data_valid) begin
                if (rx_count != $bits(rx_count)'(RX_BUFF_LEN)) begin
                    rx_buffer[rx_count]     <= rx_data;

                    if (!rx_eoc) begin
                        // don't count partial bytes. This makes our rx_count and rx_data_bits
                        // match the AC/SELECT message's NVB
                        rx_count <= rx_count + 1'd1;
                    end

                    // if rx_count is 2,3,4,5,6 (or in other words > 1) then check to see
                    // if the received data matches our UID data. This is only used if we are
                    // actually an AC / SELECT message.
                    // TODO: compare area usage with if (rx_count[2:1] != 0)
                    if (rx_count > 1) begin
                        if (!rx_matches_uid_data_byte) begin
                            // not for us
                            is_AC_SELECT_for_us <= 1'b0;
                        end
                    end
                end
            end
        end
    end

    // ========================================================================
    // Detect the various messages that we care about
    // ========================================================================

    // Messages we care about (see ISO/IEC 14443-3:2016 section 6.5.1)
    // -------------------------------------------------
    // MSG     HAS CRC     REPLY WITH      REPLY HAS CRC
    // -------------------------------------------------
    // REQA    no          ATQA            no
    // WUPA    no          ATQA            no
    // HLTA    yes         NO REPLY        no
    // AC      no          AC              no
    // SELECT  yes         SAK             yes

    // cast the rx_buffer to the AntiCollisionSelectCommand struct
    AntiCollisionSelectCommand ac_sel_msg;
    assign ac_sel_msg = AntiCollisionSelectCommand'(rx_buffer);

    logic is_REQA;
    logic is_WUPA;
    logic is_HLTA;
    logic is_AC_SELECT_NVB_valid;   // is the NVB in the ac_sel_msg valid
    logic is_AC_SELECT;             // is AC or SELECT
    logic is_SELECT;                // is SELECT (not AC)

    // we could make these checks more precise, by checking we have the exact correct amount of bits
    // However I'm not sure it's necesarry. if we are in the idle state waiting REQA and there's
    // a REQA in the correct bits of the first byte, then it's probably meant to be a REQA and
    // not something else / corrupt.
    assign is_REQA                  = (rx_buffer[0][6:0] == REQA); /* &&
                                      (rx_count == 1)               &&
                                      (rx_data_bits == 7); */

    assign is_WUPA                  = (rx_buffer[0][6:0] == WUPA); /* &&
                                      (rx_count == 1)               &&
                                      (rx_data_bits == 7); */

    assign is_HLTA                  = (rx_buffer[0] == HLTA[7:0])   &&
                                      (rx_buffer[1] == HLTA[15:8])  &&
                                      rx_crc_ok;                   /* &&
                                      (rx_count == 4)               && // 2 bytes HLTA + 2 bytes CRC
                                      (rx_data_bits == 0); */

    assign is_AC_SELECT             = (ac_sel_msg.cascadeLevel == current_cascade_level_code); /* &&
                                      (ac_sel_msg.nvb.bits  == rx_data_bits)                    &&
                                      (ac_sel_msg.nvb.bytes == rx_count); */

    assign is_SELECT                = is_AC_SELECT                  &&
                                      rx_crc_ok                     &&
                                      (ac_sel_msg.nvb.bits == 0)    &&
                                      (ac_sel_msg.nvb.bytes == 7);

    // ========================================================================
    // State machine
    // ========================================================================

    // See ISO/IEC 14443-3:2016 section 6.3 PICC states
    typedef enum
    {
        //State_POWER_OFF,          // we don't use this, because if we are powered on
                                    // then there's an RF field, or it's just disabled
                                    // and we're about to power off
        State_IDLE,
        State_READY,
        State_ACTIVE,
        State_PROTOCOL

        // we use a separate state_star bit for this
        //State_HALT,
        //State_READY_STAR,
        //State_ACTIVE_STAR
    } State;

    State state;
    logic state_star;
    State next_state;
    logic next_state_star;

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            state       <= State_IDLE;
            state_star  <= 1'b0;
        end
        else begin
            state       <= next_state;
            state_star  <= next_state_star;
        end
    end

    enum
    {
        Reply_NONE,
        Reply_ATQA,
        Reply_AC,
        Reply_SAK
    } reply;

    always_comb begin
        // assign defaults to prevent latches
        next_state          = state;
        next_state_star     = state_star;
        reply               = Reply_NONE;
        next_cascade_level  = current_cascade_level;

        // do nothing if we haven't received a packet (except if we are State_PROTOCOL
        // and the deselect command is detected in the 14443-4 block)
        if (pkt_received) begin
            // See ISO/IEC 14443-3:2016 section 6.3 PICC states

            // on an error we return to State_IDLE (state_star remains the same)
            if (rx_error_flag) begin
                if ((state == State_READY) || (state == State_ACTIVE)) begin
                    next_state = State_IDLE;
                end
                else begin
                    // in other states we stay where we are, either we're already in IDLE
                    // or we're in PROTOCOL which handles it's own messages.
                end
            end
            else begin
                // no error so process valid transitions

                case (state)
                    State_IDLE: begin
                        // If we are !state_star and we get REQA / WUPA
                        // or if we are state_star and we get WUPA, then go to READY and send ATQA
                        // otherwise remain idle
                        if ((is_REQA && !state_star) || is_WUPA) begin
                            next_state          = State_READY;
                            reply               = Reply_ATQA;
                            next_cascade_level  = '0;
                        end
                    end

                    State_READY: begin
                        // If it's a SELECT for us then move on to the next cascade level
                        // or if done then got to State_ACTIVE.
                        // if it's a AC and matches us, then stay here
                        // for all other messages return to idle
                        if (is_AC_SELECT && is_AC_SELECT_for_us) begin
                            if (is_SELECT) begin
                                if (is_final_cascade_level) begin
                                    next_state = State_ACTIVE;
                                end
                                else begin
                                    next_cascade_level = next_cascade_level + 1'd1;
                                end
                                reply = Reply_SAK;
                            end
                            else begin
                                reply = Reply_AC;
                            end
                        end
                        else begin
                            next_state = State_IDLE;
                        end
                    end

                    State_ACTIVE: begin
                        // if it's RATS then go to State_PROTOCOL
                        // if it's HLTA then go to State_IDLE + set state_star
                        // for anything else go to State_IDLE

                        // TODO: Maybe move RATS detection and decode to the 14443-4 block?
                        //       when in the active state we direct the rx data to the
                        //       14443-4 block and this initialisation module
                        //       when in the protocol state we just direct it to the 14443-4 block
                        //       ??
                        /* if (is_RATS) begin
                            next_state = State_PROTOCOL;
                        end
                        else */ begin
                            next_state = State_IDLE;
                        end

                        if (is_HLTA) begin
                            next_state_star = 1'b1;
                        end
                    end

                    State_PROTOCOL: begin
                        // we shouldn't ever receive messages while in the PROTOCOL state
                        // just remain in this state
                    end

                    default: begin
                        // shouldn't be here, revert to IDLE
                        next_state = State_IDLE;
                    end

                endcase
            end
        end
        else if ((state == State_PROTOCOL) && iso14443_4_deselect) begin
            // the ISO 14443-4 block has received the DESELECT command
            // go to idle + star
            next_state      = State_IDLE;
            next_state_star = 1'b1;
        end
    end

    // ========================================================================
    // Replies
    // ========================================================================

    // biggest reply is the AC command when 0 bits of the UID are sent by the PCD
    // the PICC replies with the 4 bytes of UID + BCC
    localparam int TX_BUFF_LEN = 5;
    logic [7:0]     tx_buffer [TX_BUFF_LEN];
    logic [2:0]     tx_count_minus_1;
    logic [2:0]     tx_bytes_to_shift;
    logic [2:0]     tx_bits_to_shift;

    // Our ATQA response
    localparam logic [15:0] ATQA_REPLY = ATQA(UID_SIZE);

    assign tx_data = tx_buffer[0];

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            tx_ready_to_send    <= 1'b0;
            tx_bytes_to_shift   <= '0;
            tx_bits_to_shift    <= '0;
        end
        else begin
            // tx_ready_to_send is cleared when the tx_req asserts
            // and we are out of stuff to send
            // it gets set when reply is not Reply_NONE

            // deal with byte and bit shifting as part of the AC reply (see Reply_AC below)
            if (tx_bytes_to_shift) begin
                tx_bytes_to_shift <= tx_bytes_to_shift - 1'd1;
                // shift tx_buffer
                for (int i = 0; i < (TX_BUFF_LEN - 1); i++) begin
                    tx_buffer[i] <= tx_buffer[i+1];
                end
            end
            else if (tx_bits_to_shift) begin
                tx_bits_to_shift <= tx_bits_to_shift - 1'd1;
                // shift tx_buffer[0] right by 1
                tx_buffer[0][6:0] <= tx_buffer[0][7:1];
            end

            // Deal with the Tx module requesting more data
            if (tx_req) begin
                // anything more to send?
                if (tx_count_minus_1) begin
                    // yes, decrement tx_count_minus_1
                    tx_count_minus_1    <= tx_count_minus_1 - 1'd1;

                    // all transfers from the PICC are 8 bits wide
                    // except the first of the AC reply
                    tx_data_bits        <= 3'd0; // 0 -> 8 bits

                    // shift tx_buffer
                    for (int i = 0; i < (TX_BUFF_LEN - 1); i++) begin
                        tx_buffer[i]    <= tx_buffer[i+1];
                    end
                end
                else begin
                    // nope
                    tx_ready_to_send <= 1'b0;
                end
            end

            // are we meant to send anything new?
            case (reply)
                Reply_ATQA: begin
                    // LSByte first
                    tx_buffer[0]        <= ATQA_REPLY[7:0];
                    tx_buffer[1]        <= ATQA_REPLY[15:8];
                    tx_count_minus_1    <= 3'd1;    // send 2 bytes
                    tx_append_crc       <= 1'b0;
                    tx_ready_to_send    <= 1'b1;
                    tx_data_bits        <= 3'd0;    // first tfer is 8 bits wide
                end
                Reply_AC: begin
                    // we have many ticks before we start to send
                    // so we copy all the data in here and then
                    // shift it one byte at a time to get the correct starting byte
                    // and then one bit at a time to get the correct starting bit
                    // this saves us needing an expensive barrel shifter
                    tx_buffer[0]        <= current_cascade_uid_data.uid[7 : 0];
                    tx_buffer[1]        <= current_cascade_uid_data.uid[15: 8];
                    tx_buffer[2]        <= current_cascade_uid_data.uid[23:16];
                    tx_buffer[3]        <= current_cascade_uid_data.uid[31:24];
                    tx_buffer[4]        <= current_cascade_uid_data.bcc;

                    tx_bytes_to_shift   <= ac_sel_msg.nvb.bytes - 2'd2;
                    tx_bits_to_shift    <= ac_sel_msg.nvb.bits;

                    // for the first transfer send 8 - ac_sel_msg.nvb.bits
                    // since it's 3 bits wide, 0 is the same as 8.
                    // 0 - 0 =  0 = 3'd000 = 0 -> send 8 bits
                    // 0 - 1 = -1 = 3'd111 = 7 -> send 7 bits
                    // 0 - 7 = -7 = 3'd001 = 1 -> send 1 bit
                    tx_data_bits        <= 3'd0 - ac_sel_msg.nvb.bits;

                    // we have received nvb.bytes - 2, full bytes of the UID + BCC (5 bytes)
                    // so we need to send 5 - (nvb.bytes - 2) = 7 - nvb.bytes
                    // tx_count_minus_1 is -1 of what we actually want, so 6 - nvb.bytes
                    tx_count_minus_1    <= 3'd6 - ac_sel_msg.nvb.bytes;
                    tx_append_crc       <= 1'b0;
                    tx_ready_to_send    <= 1'b1;
                end
                Reply_SAK: begin
                    tx_buffer[0]        <= (is_final_cascade_level) ? SAK_UID_COMPLETE
                                                                    : SAK_UID_NOT_COMPLETE;
                    tx_count_minus_1    <= 3'd0;    // send 1 byte
                    tx_append_crc       <= 1'b1;
                    tx_ready_to_send    <= 1'b1;
                    tx_data_bits        <= 3'd0;    // first tfer is 8 bits wide
                end
            endcase
        end
    end

    // ========================================================================
    // Verification
    // ========================================================================

    // make sure UID_SIZE and UID_INPUT_BITS are valid
    // since we don't have synth time assertions / errors
    // instantiate a none existing module
    generate
        // is the UID_SIZE a valid enum item?
        if (get_uid_bits(UID_SIZE) == 0) begin
            synth_time_error uid_size_invalid(.*);
        end

        // we can't have more bits in the uid port than in the entire UID
        // also we need at least 1 bit in the uid port
        if ((UID_INPUT_BITS > get_uid_bits(UID_SIZE)) ||
            (UID_INPUT_BITS == 0)) begin
            synth_time_error uid_input_bits_invalid(.*);
        end
    endgenerate

    // confirm the size of some structs used here
    // This may seems unecessary but I've seen this issue before.
    initial begin: acSelSizeChecks
        nvbSize:        assert ($bits(NVB) == 8)
                            else $fatal(1, "struct NVB is not of the correct size");
        uidDataSize:    assert ($bits(UIDData) == 40)
                            else $fatal(1, "struct UIDData is not of the correct size");
        acSelSize:      assert ($bits(AntiCollisionSelectCommand) == 56)
                            else $fatal(1, "struct AntiCollisionSelectCommand is not of the correct size");
    end

endmodule
