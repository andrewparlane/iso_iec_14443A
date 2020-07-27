/***********************************************************************
        File: iso14443_4a.sv
 Description: Parses iso14443-4[a] messages
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

// The majority of ISO/IEC 14443-4 does not distinguish between PICCs of types A or B
// however PICCs of type A have an additional init steps defined in section 5.
// Namely the RATS -> ATS and the PPS -> PPS response messages.
// As such I'm calling this the iso14443_4a module for now. If at somepoint we want to
// expand this IP core to support both type A and B PICCs then this will need a bit of reworking

// There are a few features of ISO/IEC 14443-4 that we don't currently support:
//  NAD                 - Node Address, this allows us to have multiple applications (endpoints).
//  I-Block chaining    - If the PCD / PICC want to send a message that is larger than the FSD / FSC
//                        of the receiver, then that message can be split into multiple blocks with chaining
//                        The minimum supported FSD / FSC is 16 bytes (including header + CRC, so 12 bytes INF)
//                        I currently don't have any need to support messages greater than 12 bytes.
//                        And since we have control of both the PCD and PICC we can just design the app
//                        comms to meet this restriction.
// FWT                  - Frame Waiting Time, this is the length of time that the PICC has to respond to a
//                        message from the PCD. I currently require the message to be sent after the FDT
//                        (frame delay time) which is the case for all the initialisation messages
// WTX                  - Wait Time Extension, if the PICC is not ready to respond in time to a PCD message
//                        it can send a WTX to ask for more time. Since I require all replies to be sent after
//                        the FDT, there is no point in supporting this. If at some point somebody needs to
//                        use this IP core with an app that needs longer than the FDT to respond, then some
//                        rework will be required to allow sending messages after the FDT but within the FWT,
//                        and to be able to send the WTX to request more time.
// Enhanced Blocks      - This type of block allows error recovery, instead of just detection. This isn't
//                        necesarry for us, and would add a lot more complexity to this IP core to support it.
// PARAMETERS           - The parameters message lets you change bit rates and to enable enhanced blocks
//                        since we don't support other bit rates or enhanced blocks we do not support this
//                        message, as per the standard we ignore any S(PARAMETERS) requests.

// It doesn't break the standard to not support most of these, the only exception is I-block chaining.
// So it may be worthwhile implementing that. However we have no use for it in the current intended
// application, and since we control the PCD we don't have to worry about what happens if chained I-blocks
// are sent.
// TODO: Implement I-Block chaining

module iso14443_4a
(
    // clk is our 13.56MHz input clock. It is recovered from the carrier wave,
    // and as such stops during pause frames. It must not have any glitches.
    input                       clk,

    // rst is our active low synchronised asynchronous reset signal
    input                       rst_n,

    // Every reply from the PICC that includes a CID field also includes a power indicator
    // field to tell the PCD if it's receiving enough power or not.
    // The analogue block should pass the correct value in. It can change over time.
    // and is synchronised (in the iso14443a top level module). 2'b00 should be passed
    // if this is not supported
    input [1:0]                 power,

    // To / From the 14443-3 layer
    rx_interface.in_byte        rx_iface,
    input                       rx_crc_ok,
    tx_interface.out_byte       tx_iface,
    output logic                tx_append_crc,

    // ISO/IEC 14443-3 control signals
    input                       tag_active,         // next message must be RATS
    // rx_rats must be asserted when the iso14443_3a.initialisation module asserts pkt_received
    // otherwise it will interpret this message as not a RATS and count it as an error.
    output logic                rx_rats,            // got the RATS         (part3a go to State_PROTOCOL)
    output logic                rx_deselect,        // received a DESELECT  (part3a go to State_HALT)

    // To / From app layer
    rx_interface.out_byte       app_rx_iface,
    tx_interface.in_byte        app_tx_iface,
    output logic                app_resend_last     // asserted for one tick to indicate the APP should resend it's last message
);

    import ISO14443A_pkg::*;

    // we only deal in full bytes
    assign app_rx_iface.data_bits   = '0;

    // ========================================================================
    // Clock in the Rx message and detect errors
    // ========================================================================

    // The largest message we could receive is the PPS message
    // consisting of 5 bytes
    localparam int  RX_BUFF_LEN = 5;
    logic [7:0]     rx_buffer [RX_BUFF_LEN];
    logic [2:0]     rx_count;
    logic           rx_error_flag;
    logic           pkt_received;
    logic [3:0]     our_cid;
    logic           check_need_to_forward_to_app;
    logic           check_need_to_forward_to_app_after_next_byte;
    logic           forward_to_app;

    logic           is_valid_iso14443_4_msg;
    logic           is_RATS;
    logic           is_PPS;
    logic           is_I_BLOCK;
    logic           is_R_BLOCK;
    logic           is_S_BLOCK;
    logic           has_CID;
    logic           has_NAD;
    logic           is_for_us;    // CID for us
    logic           is_CHAINING;
    logic           is_NAK;
    logic           is_DESELECT;
    logic           rx_block_num;

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            rx_count                    <= '0;
            rx_error_flag               <= 1'b0;
            pkt_received                <= 1'b0;
            forward_to_app              <= 1'b0;
            app_rx_iface.soc            <= 1'b0;
            app_rx_iface.eoc            <= 1'b0;
            app_rx_iface.data_valid     <= 1'b0;
            app_rx_iface.error          <= 1'b0;
        end
        else begin
            // these should only assert for one tick at a time
            pkt_received                    <= 1'b0;
            check_need_to_forward_to_app    <= 1'b0;
            app_rx_iface.soc                <= 1'b0;
            app_rx_iface.eoc                <= 1'b0;
            app_rx_iface.data_valid         <= 1'b0;
            app_rx_iface.error              <= 1'b0;

            // always pass through the data
            app_rx_iface.data               <= rx_iface.data;

            if (rx_iface.soc) begin
                // start of a new message
                rx_count                                        <= '0;
                rx_error_flag                                   <= 1'b0;
                forward_to_app                                  <= 1'b0;
                check_need_to_forward_to_app_after_next_byte    <= 1'b0;
            end

            if (rx_iface.eoc) begin
                // we use this rather than rx_eoc directly,
                // because for partial packets the rx_iface.data_valid assserts
                // at the same time, and so our rx_buffer won't be correct
                // until the next tick.
                pkt_received    <= 1'b1;

                if (forward_to_app) begin
                    app_rx_iface.eoc    <= 1'b1;
                    app_rx_iface.error  <= !rx_crc_ok;  // error if the CRC failed
                    forward_to_app      <= 1'b0;
                end
            end

            // don't do anything once we've seen an error
            if (!rx_error_flag) begin
                if (rx_iface.error) begin
                    rx_error_flag <= 1'b1;
                    if (forward_to_app) begin
                        app_rx_iface.error  <= 1'b1;
                    end
                end

                if (rx_iface.data_valid) begin
                    if (forward_to_app) begin
                        app_rx_iface.data_valid <= 1'b1;
                    end

                    if (rx_count != $bits(rx_count)'(RX_BUFF_LEN)) begin
                        rx_buffer[rx_count] <= rx_iface.data;
                        rx_count            <= rx_count + 1'd1;

                        // If this is a valid I-block that's for us, we need to forward everything
                        // after the prologue field to the APP.
                        // There are two options here:
                        //      1) after receiving the first byte, we find that it's a STD I-Block
                        //         with no chaining, no NAD, and no CID, and our CID is 0, so it's
                        //         valid and for us. The next byte is the first byte of the INF field
                        //      2) after receiving the first byte, we find that it's a STD I-BLock
                        //         with no chaining, no NAD, and a CID. After the second byte we know
                        //         if it's for us or not. After that we start forwarding it to the app.
                        // We do the checking on the next tick, so we can use the is_... and has_...
                        // signals that depend on the data to be in the rx_buffer.
                        if (rx_count == 0) begin
                            // on the next tick, see if we are a STD I-block with no chaining and no NAD
                            check_need_to_forward_to_app <= 1'b1;
                        end
                        else if (check_need_to_forward_to_app_after_next_byte) begin
                            // just received the second byte, so on the next tick check if
                            // the CID is for us.
                            check_need_to_forward_to_app                    <= 1'b1;
                            check_need_to_forward_to_app_after_next_byte    <= 1'b0;
                        end
                    end
                end

                // don't forward anything if the tag is in the ACTIVE state. As we shouldn't
                // respond to STD I-BLock until we are in the PRTOCOL state.
                if (check_need_to_forward_to_app && !tag_active) begin
                    // Now we're on the next tick, check if the data received is a valid STD I-BLock
                    if (is_I_BLOCK && !has_NAD && !is_CHAINING) begin
                        // Is a valid I-BLock, is it for us?
                        // this could happen after the first byte if there's no CID and our CID is 0
                        // or after the second byte if there is a CID
                        if ((rx_count == 1) && has_CID) begin
                            // we don't know if it's for us yet. wait until the next byte.
                            check_need_to_forward_to_app_after_next_byte <= 1'b1;
                        end
                        else begin
                            // either rx_count == 1 and the message doesn't have a CID
                            // so is_for_us reduces to (our_cid == 0).
                            // or rx_count == 2 and has_CID is true, since we wouldn't get here otherwise
                            // in which case is_for_us reduces to our_cid == rx_buffer[1][3:0]
                            // either way we can use is_for_us to determine if we forward this message
                            // to the app
                            if (is_for_us) begin
                                // start forwarding to the app
                                forward_to_app      <= 1'b1;

                                // start with SOC
                                app_rx_iface.soc    <= 1'b1;
                            end
                        end
                    end
                end
            end
        end
    end

    // ========================================================================
    // Detect the various messages that we care about
    // ========================================================================

    // For it to be a valid ISO/IEC 14443-4 message
    assign is_valid_iso14443_4_msg  = rx_crc_ok                 &&
                                      !rx_error_flag;

    assign is_RATS                  = (rx_buffer[0] == RATS)    &&
                                      (rx_count == 4)           &&  // 2 bytes + 2 bytes CRC
                                      (rx_buffer[1][3:0] != 4'hF);  // CID must not be 15

    // tell the iso14443_3a.initialisation module that this is a RATS message
    // we do this with combinatory logic, because it has to be quick enough
    // that the initialisation block gets it in time.
    assign rx_rats                  = is_valid_iso14443_4_msg &&
                                      is_RATS;

    // We don't really need to support PPS. Since we don't support any other bit rates
    // this message is useless. However ISO/IEC 14443-4:2016 section 5.6.2.2 a) states
    // that when the PICC receives a valid PPS request, the PICC "shall" send the PPS response.
    // so to be in spec we must support this message

    // We could potentially skimp on the checks here to save area?
    // However the below checks the PPS message is correct thus we must reply
    assign is_PPS                   = (rx_buffer[0] == {PPSS, our_cid}) &&
                                      (((rx_count == 4) && (rx_buffer[1] == 8'h01)) ||
                                       ((rx_count == 5) && (rx_buffer[1] == 8'h11) &&
                                                           (rx_buffer[2] == 8'h00)));

    assign is_I_BLOCK               = rx_buffer[0] ==? 8'b000???1?;
    assign is_R_BLOCK               = rx_buffer[0] ==? 8'b101??01?;
    assign is_S_BLOCK               = rx_buffer[0] ==? 8'b11???0?0;
    assign has_CID                  = rx_buffer[0][3];
    assign has_NAD                  = rx_buffer[0][2];

    // ISO/IEC 14443-4 section 7.1.2.2 states:
    //  A PICC which supports a CID (we do)
    //  shall respond to blocks containing it's CID
    //  shall, in case it's CID is 0, respond also to blocks containing no CID
    assign is_for_us                = has_CID ? (our_cid == rx_buffer[1][3:0]) : (our_cid == 0);

    assign is_CHAINING              = rx_buffer[0][4];
    assign is_NAK                   = rx_buffer[0][4];
    assign is_DESELECT              = rx_buffer[0] ==? 8'b??00??1?;
    assign rx_block_num             = rx_buffer[0][0];

    // ========================================================================
    // Control logic
    // ========================================================================

    logic allow_pps;        // PPS may only come immediately after we have received RATS and sent our ATS

    enum
    {
        Reply_ATS,
        Reply_PPSR,
        Reply_STANDARD_BLOCK
    } reply;

    enum
    {
        // S()
        ReplyStdBlock_DESELECT,

        // R()
        ReplyStdBlock_ACK,

        // I()
        ReplyStdBlock_I_BLOCK
    } replyStdBlock;

    logic send_reply;
    logic our_block_num;

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            allow_pps       <= 1'b0;
            app_resend_last <= 1'b0;
        end
        else begin
            // should only assert for one tick
            send_reply      <= 1'b0;
            app_resend_last <= 1'b0;

            if (pkt_received) begin
                // if we've received anything at all, whether it be PPS or not
                // then we no longer allow PPS messages
                // this can be overriden if we received a valid RATS while the tag was active
                allow_pps <= 1'b0;

                if (is_valid_iso14443_4_msg) begin
                    if (tag_active) begin
                        // only valid thing to receive is RATS
                        if (rx_rats) begin
                            // received RATS
                            our_cid                 <= rx_buffer[1][3:0];
                            // we ignore FSDI since we don't support chaining
                            // for future reference:
                            // ISO/IEC 14443-4:2016 section 5.1: A PCD setting FSDI = 'D' - 'F'
                            // is not compliant with this part of ISO/IEC 14443. Until the RFU
                            // values 'D' - 'F' are assigned by ISO/IEC, a PICC receiving values
                            // of FSDI = 'D' - 'F' should interpret it as FSDI = 'C'
                            //fsdi                    <= rx_buffer[1][7:4];

                            // respond with out ATS
                            reply                   <= Reply_ATS;
                            send_reply              <= 1'b1;

                            // we allow PPS as the next message
                            // but others are valid too
                            allow_pps               <= 1'b1;

                            // Rule C: The PICC block number shall be initialised to 1 at activation
                            our_block_num           <= 1'b1;
                        end
                    end
                    else begin
                        // first message after RATS can be a PPS
                        if (allow_pps && is_PPS) begin
                            reply       <= Reply_PPSR;
                            send_reply  <= 1'b1;

                            // note: above we clear allow_pps upon receiving any packet
                            //       valid or not, pps or not
                        end
                        // others messages are also allowed
                        else if (is_for_us && !has_NAD) begin // we don't support frames with the NAD field

                            // we've received our RATS so we can now receive standard blocks
                            // we don't have to worry about a PPS / another RATS being picked up here
                            // as their first bytes don't match bit patterns for the first byte of any
                            // standard block.

                            if (is_S_BLOCK) begin
                                // ISO/IEC 14443-4:2016 section 7.5.5
                                // Rule 3: S-Blocks are only used in pairs
                                if (is_DESELECT) begin
                                    // send the DESELECT reply
                                    reply           <= Reply_STANDARD_BLOCK;
                                    replyStdBlock   <= ReplyStdBlock_DESELECT;
                                    send_reply      <= 1'b1;

                                    // after our reply has been sent rx_deselect is asserted
                                    // which causes the iso14443_3a module to go to the HALT state
                                end
                                // Other S-Blocks are: S(PARAMETERS) and S(WTX).
                                // The PCD can't send S(WTX).
                                // ISO/IEC 14443-4:2016 section 9, states:
                                //      if the PICC supports S(PARAMETERS) blocks, the PICC shall
                                //      respond with an S(PARAMETERS) block containing values for
                                //      all supported parameters. If the PICC does not support
                                //      S(PARAMETERS) it shall stay mute.
                                // So we ignore any other S-Block
                            end
                            else if (is_R_BLOCK) begin
                                // ISO/IEC 14443-4:2016 section 7.5.5
                                // Rule 11: When an R(ACK)/R(NAK) block is received, if it's
                                //          block number is equal to the PICC's current block
                                //          number, the last block shall be retransmitted
                                if (rx_block_num == our_block_num) begin
                                    // resend last message
                                    // reply and replyStdBlock are already set
                                    send_reply      <= 1'b1;

                                    // if the last message sent was an I-Block
                                    // tell the app to resend it's last message
                                    if ((reply == Reply_STANDARD_BLOCK) &&
                                        (replyStdBlock == ReplyStdBlock_I_BLOCK)) begin
                                        app_resend_last <= 1'b1;
                                    end
                                end
                                else begin
                                    if (is_NAK) begin
                                        // R(NAK)
                                        // Rule 12: When an R(NAK) block is received, if it's block number
                                        //          is not equal to the PICC's current block number an R(ACK)
                                        //          block shall be sent
                                        reply           <= Reply_STANDARD_BLOCK;
                                        replyStdBlock   <= ReplyStdBlock_ACK;
                                        send_reply      <= 1'b1;

                                        // ISO/IEC 14443-4:2016 section 7.5.4.2 Block Numbering Rules (PICC rules)
                                        // Rule E Note 2: There is no block toggling when an R(NAK) block is received
                                    end
                                    else begin
                                        // R(ACK)
                                        // Rule 13:  When an R[ACl{] block is received, if its block
                                        //           number is not equal to the PICC’s current block
                                        //           number, and the PICC is in chaining, chaining
                                        //           shall be continued.

                                        // we don't support chaining so no need to do anything

                                        // ISO/IEC 14443-4:2016 section 7.5.4.2 Block Numbering Rules (PICC rules)
                                        // Rule E: When an R(ACK) block with a block number not equal to the current
                                        //         PICC's block number is received, the PICC shall toggle it's block
                                        //         number before sending a block.
                                        /* if (rx_block_num != our_block_num) begin
                                            our_block_num   <= !our_block_num;
                                        end */
                                    end
                                end
                            end
                            else if (is_I_BLOCK && !is_CHAINING) begin
                                // ISO/IEC 14443-4:2016 section 7.5.5
                                // Rule 10: When an I-Block not indicating chaining is received
                                //          The block shall be acknowledged with an I-Block
                                // respond with an I block
                                reply                   <= Reply_STANDARD_BLOCK;
                                replyStdBlock           <= ReplyStdBlock_I_BLOCK;
                                send_reply              <= 1'b1;

                                // ISO/IEC 14443-4:2016 section 7.5.4 Block Numbering Rules
                                // Rule D: When an I-block is received, the PICC shall toggle it's block number
                                //         before sending a block.
                                our_block_num           <= !our_block_num;

                                // Rule D, Note 1:
                                // The PICC can check if the received block number is not in compliance with PCD rules
                                // to decide neither to toggle its internal block number nor to send a response block.

                                // I don't think this is necessary since it says "can", and if the PCD
                                // follows the error detection and recovery rules, we should never end up
                                // with this issue.
                            end
                        end
                    end
                end
            end
        end
    end

    // ========================================================================
    // Replies
    // ========================================================================

    // The longest reply we send is 2 bytes + CRC
    localparam int TX_BUFF_LEN = 2;
    logic [7:0]     tx_buffer [TX_BUFF_LEN];
    logic [0:0]     tx_count_minus_1;
    logic           forward_from_app;

    assign tx_append_crc        = 1'b1;         // part4 comms always have the CRC appended
    assign tx_iface.data        = tx_buffer[0];
    assign tx_iface.data_bits   = 3'd0;         // all transfers from the PICC are 8 bits wide

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            tx_iface.data_valid     <= 1'b0;
            forward_from_app        <= 1'b0;
            rx_deselect             <= 1'b0;
            app_tx_iface.req        <= 1'b0;
        end
        else begin
            // these are only asserted for one tick
            app_tx_iface.req        <= 1'b0;
            rx_deselect             <= 1'b0;

            // tx_iface.data_valid is cleared when the tx_iface.req asserts and we are out of
            // stuff to send. tx_iface.data_valid gets set when reply is not Reply_NONE

            // Deal with the Tx module requesting more data
            if (tx_iface.req) begin
                // anything more to send?
                if (tx_count_minus_1) begin
                    // yes, decrement tx_count_minus_1
                    tx_count_minus_1    <= tx_count_minus_1 - 1'd1;

                    // shift tx_buffer
                    for (int i = 0; i < (TX_BUFF_LEN - 1); i++) begin
                        tx_buffer[i]    <= tx_buffer[i+1];
                    end
                end
                else begin
                    // nothing from us, are we forwarding from the app?
                    if (forward_from_app) begin
                        // we are, is there still data to send?
                        if (app_tx_iface.data_valid) begin
                            // forward the request
                            app_tx_iface.req        <= 1'b1;
                            // fill in the data
                            tx_buffer[0]            <= app_tx_iface.data;
                        end
                        else begin
                            // no more data to send
                            tx_iface.data_valid     <= 1'b0;
                            forward_from_app        <= 1'b0;
                        end
                    end
                    else begin
                        // not forwarding from the app, so we're done
                        tx_iface.data_valid <= 1'b0;

                        // if this was a DESELECT reply, then we need to inform
                        // the 14443-3 layer to move us to the HALT state
                        if ((reply == Reply_STANDARD_BLOCK) &&
                            (replyStdBlock == ReplyStdBlock_DESELECT)) begin
                            rx_deselect <= 1'b1;
                        end
                    end
                end
            end

            // are we meant to send anything new?
            if (send_reply) begin
                case (reply)
                    Reply_ATS: begin
                        // for now we just send the minimum ATS which uses all the default options
                        tx_buffer[0]            <= 8'd1;    // first byte is TL (length including itself, not including CRC)
                        tx_count_minus_1        <= 1'd0;    // 1 byte + CRC
                        tx_iface.data_valid     <= 1'b1;
                    end
                    Reply_PPSR: begin
                        tx_buffer[0]            <= {PPSS, our_cid}; // PPS response is just the start byte
                        tx_count_minus_1        <= 1'd0;            // 1 byte + CRC
                        tx_iface.data_valid     <= 1'b1;
                    end
                    Reply_STANDARD_BLOCK: begin
                        // a standard block consists of the header, the INF field and the CRC
                        // the CRC is filled in automatically by the 14443-3 layer
                        // the INF field is only used (by us) for the I block, and that
                        // comes from the app layer.
                        // So just fill in the header

                        // PCB
                        case (replyStdBlock)
                            ReplyStdBlock_DESELECT:     tx_buffer[0] <= S_DESELECT;
                            ReplyStdBlock_ACK:          tx_buffer[0] <= R_ACK;
                            ReplyStdBlock_I_BLOCK:      tx_buffer[0] <= I_NO_CHAINING;
                        endcase

                        // The CID bit is set if the request had a CID
                        tx_buffer[0][3] <= has_CID;

                        // In the case of I-blocks and R-blocks we have to set the block num field
                        if ((replyStdBlock == ReplyStdBlock_ACK) ||
                            (replyStdBlock == ReplyStdBlock_I_BLOCK)) begin
                            tx_buffer[0][0] <= our_block_num;
                        end

                        // The next byte is the CID byte if we have one
                        if (has_CID) begin
                            tx_buffer[1]        <= {power, 2'b00, our_cid}; // power indicator + CID
                            tx_count_minus_1    <= 1'b1;                    // 2 bytes + CRC
                        end
                        else begin
                            tx_count_minus_1    <= 1'b0;                    // 1 byte + CRC
                        end

                        // The final byte is the NAD byte, but we don't support that

                        // if this is an I-block reply, we need to forward data from the app
                        if (replyStdBlock == ReplyStdBlock_I_BLOCK) begin
                            forward_from_app        <= 1'b1;
                        end

                        // set it going
                        tx_iface.data_valid     <= 1'b1;
                    end
                endcase
            end
        end
    end

endmodule
