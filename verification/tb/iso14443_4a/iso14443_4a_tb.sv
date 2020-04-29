/***********************************************************************
        File: iso14443_4a_tb.sv
 Description: Testbench for iso14443_4a
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

module iso14443_4a_tb;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic           clk;
    logic           rst_n;

    logic [1:0]     power;              // input

    logic           rx_crc_ok;          // input
    logic           tx_append_crc;      // output
    logic           tag_active;         // input
    logic           rx_rats;            // output
    logic           rx_deselect;        // output
    logic           app_resend_last;    // output

    rx_interface #(.BY_BYTE(1)) rx_iface (.*);
    tx_interface #(.BY_BYTE(1)) tx_iface (.*);
    rx_interface #(.BY_BYTE(1)) app_rx_iface (.*);
    tx_interface #(.BY_BYTE(1)) app_tx_iface (.*);

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    iso14443_4a dut (.*);

    // --------------------------------------------------------------
    // Clock generator
    // --------------------------------------------------------------

    // Calculate our clock period in ps
    localparam CLOCK_FREQ_HZ = 13560000; // 13.56MHz
    localparam CLOCK_PERIOD_PS = 1000000000000.0 / CLOCK_FREQ_HZ;
    initial begin
        clk = 1'b0;
        forever begin
            #(int'(CLOCK_PERIOD_PS/2))
            clk = ~clk;
        end
    end

    // --------------------------------------------------------------
    // The source for the rx_iface
    // --------------------------------------------------------------

    rx_interface_source rx_source
    (
        .clk    (clk),
        .iface  (rx_iface)
    );

    // --------------------------------------------------------------
    // The sink for the tx_iface
    // --------------------------------------------------------------

    tx_interface_sink tx_sink
    (
        .clk    (clk),
        .iface  (tx_iface)
    );

    // --------------------------------------------------------------
    // The source for the app_tx_iface
    // --------------------------------------------------------------

    tx_interface_source app_tx_source
    (
        .clk    (clk),
        .iface  (app_tx_iface)
    );

    // --------------------------------------------------------------
    // The sink for the app_rx_iface
    // --------------------------------------------------------------

    rx_interface_sink app_rx_sink
    (
        .clk    (clk),
        .iface  (app_rx_iface)
    );

    // --------------------------------------------------------------
    // Helper functions / tasks
    // --------------------------------------------------------------

    typedef enum
    {
        State_EXPECT_RATS,
        State_PPS_ALLOWED,
        State_OTHERS
    } State;

    typedef enum
    {
        CID_NONE,                   // don't send a CID,    RATS uses CID=0
        CID_15,                     // Use CID=15 (RFU)
        CID_CURRENT,                // use the current CID
        CID_RANDOM,                 // use any CID (0-14)
        CID_RANDOM_NOT_ZERO,        // used for CID assignment, as CID=0 has special conotations
        CID_RANDOM_NOT_CURRENT,     // use any other CID
        CID_RANDOM_WITH_15          // use any CID (0-15)
    } CidType;

    typedef enum
    {
        NAD_NONE,
        NAD_PRESENT,
        NAD_RANDOM
    } NadType;

    typedef enum
    {
        MsgType_RATS,
        MsgType_PPS,
        MsgType_I,
        MsgType_I_CHAINING,
        MsgType_ACK,
        MsgType_NAK,
        MsgType_PARAMETERS,
        MsgType_DESELECT,
        MsgType_RANDOM,
        MsgType_ERROR,
        MsgType_CORRUPTS_CRC
    } MsgType;

    // global flags
    logic       expect_rx_rats;
    logic       expect_rx_deselect;
    logic       expect_app_resend_last;

    logic       send_frame_crc_error;
    logic       send_frame_add_error;
    logic       send_frame_randomise_power;

    logic       pcd_block_num;
    logic       picc_block_num;

    logic [3:0] picc_cid;
    logic [7:0] last_received   [$];  // used for checking resends
    logic [7:0] app_last_send   [$];  // used for app_resend_last

    function logic [3:0] get_cid_from_cid_type(CidType cid_type);
        logic [3:0] cid;

        case (cid_type)
            CID_NONE:                   cid = 4'd0;
            CID_15:                     cid = 4'd15;
            CID_CURRENT:                cid = picc_cid;
            CID_RANDOM:                 cid = 4'($urandom_range(0, 14));
            CID_RANDOM_NOT_ZERO:        cid = 4'($urandom_range(1, 14));
            CID_RANDOM_NOT_CURRENT:     std::randomize(cid) with {cid != picc_cid;};
            CID_RANDOM_WITH_15:         cid = 4'($urandom_range(0, 15));
            default:                    $error("cid_type %s (%d) not supported", cid_type.name, cid_type);
        endcase

        return cid;
    endfunction

    function logic get_has_nad_from_nad_type(NadType nad_type);
        case (nad_type)
            NAD_NONE:       return 1'b0;
            NAD_PRESENT:    return 1'b1;
            NAD_RANDOM:     return $urandom;
        endcase
    endfunction

    task send_frame (logic [7:0] data[$]);
        automatic logic [15:0]  crc = frame_generator_pkg::calculate_crc(data);
        automatic int           error_in_byte = -1;

        if (send_frame_crc_error) begin
            // corrupt the CRC
            // this is not really necessary as the DUT ignores the CRC and
            // only looks at the rx_crc_ok signal.
            automatic logic [15:0] new_crc;
            std::randomize(new_crc) with {new_crc != crc;};
            crc = new_crc;
        end

        data.push_back(crc[7:0]);
        data.push_back(crc[15:8]);

        // add an error?
        if (send_frame_add_error) begin
            error_in_byte = $urandom_range(0, data.size); // not data.size-1, the last error comes before the EOC
        end

        if (send_frame_randomise_power) begin
            // randomize the power input, so we can test that it is correctly received in the reply
            std::randomize(power);
        end

        // send it and set the rx_crc_ok flag a few ticks in
        // so that it definetly won't be seen as belonging to the last frame
        fork
            // process 1 send_frame
            begin
                rx_source.send_frame(data, 0, error_in_byte);
            end

            // process 2 set rx_crc_ok flag
            begin
                // wait a few ticks to allow SOC to go out
                repeat (4) @(posedge clk) begin end
                // set the rx_crc_ok flag
                rx_crc_ok = (!send_frame_crc_error && !send_frame_add_error);
            end
        join

        // if this was a valid RATS message make sure that rx_rats is asserted
        // rx_rats must be asserted by this point, as it must be ready for when the
        // initialisation module checks the received packet
        rxRatsAsExpected: assert (rx_rats == expect_rx_rats) else $error("rx_rats %b not as expected", rx_rats);

        // If the iso14443_3a is in State_ACTIVE -> tag_active then:
        //  If rx_rats is asserted when pkt_received asserts, it moves to State_PROTOCOL
        //  Otherwise, it's treated as an error and we go to State_IDLE / State_HALT
        // Otherwise tag_active is not asserted.
        // In all cases tag_active is expected to deassert / remain deasserted
        @(posedge clk)
        tag_active = 1'b0;

        // app_resend_last should assert within a couple of ticks if it's going to
        if (expect_app_resend_last) begin
            fork
                // process 1, timeout
                begin
                    repeat (16) @(posedge clk) begin end
                    $error("app_resend_last didn't assert when expected");
                end

                // process 2 - wait for us to not be in a frame
                begin
                    wait (app_resend_last) begin end
                end

            // finish as soon as any of these processes finish
            join_any

            // disable the remaining process
            disable fork;

            @(posedge clk) begin end
        end

        // These are no longer expected, so assert if they occur
        expect_rx_rats          = 1'b0;
        expect_app_resend_last  = 1'b0;

        @(posedge clk) begin end
    endtask

    task send_rats (logic [3:0] fsdi, CidType cid_type);
        automatic logic [3:0] cid = get_cid_from_cid_type(cid_type);

        // TODO: When FSDI is supported, check that it is interpreted correctly
        //       Additionally note that values 'D' - 'F' are RFU and should be interpreted as 'C'

        // if this is a valid RATS then we expect rx_rats to assert
        if (!send_frame_add_error && !send_frame_crc_error && (cid != 15)) begin
            expect_rx_rats = 1'b1;

            // if tag_active is asserted, then the PICC treats this as the first RATS
            // and therefore we should cache some values. Otherwise this is ignored as a second RATS
            // (as though we were activating another PICC)
            if (tag_active) begin
                picc_cid = cid;
                //$display("Sent RATS activating tag with CID %d", cid);

                // ISO/IEC 14443-4:2016 section 7.5.4, Rule A
                // The PCD block number shall be initialized to 0 for each activated PICC.
                pcd_block_num = 1'b0;
                //$display("TB: Init pcd_block_num to %b", pcd_block_num);

                // Rule C
                // The PICC block number shall be initialised to 1 at activation
                picc_block_num = 1'b1;
                //$display("TB: Init picc_block_num to %b", picc_block_num);
            end
        end

        send_frame('{8'hE0, {fsdi, cid}});
    endtask

    task send_pps (CidType cid_type, logic p1_present, logic [1:0] dsi, logic [1:0] dri);
        automatic logic [7:0] pps [$];
        automatic logic [3:0] cid = get_cid_from_cid_type(cid_type);

        pps = '{{4'b1101, cid}, {3'b000, p1_present, 4'b0001}};
        if (p1_present) begin
            pps.push_back({4'b0000, dsi, dri});
        end

        //$display("sending PPS %p", pps);

        send_frame(pps);
    endtask

    task send_std_i_block (CidType cid_type, NadType nad_type, logic chaining, logic [7:0] inf [$]);
        automatic logic [7:0]   data [$];
        automatic logic [3:0]   cid             = get_cid_from_cid_type(cid_type);
        automatic logic         has_cid         = (cid_type != CID_NONE);
        automatic logic         has_nad         = get_has_nad_from_nad_type(nad_type);
        automatic logic         for_dut         = has_cid ? (cid == picc_cid) : (picc_cid == 0);
        automatic logic         tag_was_active  = tag_active;

        // PCB
        data = '{{3'b000, chaining, has_cid, has_nad, 1'b1, pcd_block_num}};
        // CID
        if (has_cid) begin
            data.push_back({2'b00, 2'b00, cid});
        end
        // NAD
        if (has_nad) begin
            data.push_back($urandom);
        end

        // INF
        foreach (inf[i]) begin
            data.push_back(inf[i]);
        end

        //$display("Sending std I-block: %p", data);

        send_frame(data);

        // Handle checking the forwarding to the app (and pcd_block_num toggling)
        if (has_nad || chaining || !for_dut || tag_was_active) begin
            // check that the app receives nothing
            check_not_forwarded_to_app;
        end
        else if (send_frame_crc_error) begin
            // check that the app receives the data, but with an error
            app_verify_rx_data(inf, 1'b1);
        end
        else if (send_frame_add_error) begin
            // check that the app either receives nothing (error in the prologue field
            // or it receives an error (error in the INF field).
            app_verify_no_data_or_error;
        end
        else begin
            // this was for us and had no errors, so should be forwarded to the app
            // check the app received it OK
            app_verify_rx_data(inf);

            // send the reply from the app
            // max 12 bytes (see recv_frame timeout comment)
            send_app_reply(frame_generator_pkg::generate_byte_queue($urandom_range(12)));

            // ISO/IEC 14443-4:2016 section 7.5.4.2, Rule D
            // When an I-block is received, the PICC shall toggle its block number before sending a block.
            picc_block_num = !picc_block_num;
            //$display("TB: sent std I-block for the PICC, toggling picc_block_num %d", picc_block_num);
        end
    endtask

    task send_std_r_block (CidType cid_type, logic nak);
        automatic logic [7:0]   data [$];
        automatic logic [3:0]   cid         = get_cid_from_cid_type(cid_type);
        automatic logic         has_cid     = (cid_type != CID_NONE);

        // PCB
        data = '{{3'b101, nak, has_cid, 2'b01, pcd_block_num}};
        // CID
        if (has_cid) begin
            data.push_back({2'b00, 2'b00, cid});
        end

        send_frame(data);
    endtask

    task send_std_s_block (CidType cid_type, logic [1:0] b6_5, logic b2, logic [7:0] inf [$]);
        automatic logic [7:0]   data [$];
        automatic logic [3:0]   cid         = get_cid_from_cid_type(cid_type);
        automatic logic         has_cid     = (cid_type != CID_NONE);

        // PCB
        data = '{{2'b11, b6_5, has_cid, 1'b0, b2, 1'b0}};
        // CID
        if (has_cid) begin
            data.push_back({2'b00, 2'b00, cid});
        end
        // INF
        foreach (inf[i]) begin
            data.push_back(inf[i]);
        end

        //$display("sending S-Block %p", data);

        send_frame(data);
    endtask

    task send_std_s_parameters (CidType cid_type, logic [7:0] inf [$]);
        send_std_s_block (cid_type, 2'b11, 1'b0, inf);
    endtask

    task send_std_s_deselect (CidType cid_type);
        send_std_s_block (cid_type, 2'b00, 1'b1, '{});
    endtask

    task send_std_r_ack (CidType cid_type);
        send_std_r_block (cid_type, 1'b0);

        // We don't support chaining, so the PCD should never send an R(ACK) thus we do not
        // follow this rule ATM.

        // ISO/IEC 14443-4:2016 section 7.5.4.2, Rule E
        // When an R(ACK) block with a block number not equal to the current PlCC’s block number
        // is received, the PICC shall toggle its block number before sending a block.
        /* if (pcd_block_num != picc_block_num) begin
            picc_block_num = !picc_block_num;
        end */
    endtask

    task send_std_r_nak (CidType cid_type);
        send_std_r_block (cid_type, 1'b1);
    endtask

    task send_random;
        automatic int           bytes_to_send = $urandom_range(1, 10);
        automatic logic [7:0]   first_byte;
        automatic logic [7:0]   data [$];

        // we don't want to match valid data (RATS, PPS, STD block), this is only
        // based on the first byte
        std::randomize(first_byte) with
        {
            first_byte                          != 8'hE0;       // RATS
            first_byte[7:4]                     != 4'b1101;     // PPS
            {first_byte[7:5], first_byte[1]}    != 4'b0001;     // I block
            {first_byte[7:5], first_byte[2:1]}  != 5'b10101;    // R block
            {first_byte[7:4], first_byte[2:0]}  != 7'b1111000;  // S(PARAMETERS)
            {first_byte[7:4], first_byte[2:0]}  != 7'b1100010;  // S(DESELECT)
        };

        data.push_back(first_byte);

        for (int i = 1; i < bytes_to_send; i++) begin
            data.push_back(8'($urandom));
        end

        send_frame(data);
    endtask

    // corrupt_crc / error change the global send_frame_add_error / send_frame_crc_error flags
    // and recall send_msg with all options enabled. AKA it will send any frame but with an error
    // or CRC error.
    task automatic send_msg(input logic     RATS,               input logic     PPS,
                            input logic     std_i_block,        input logic     std_i_block_chaining,
                            input logic     std_r_ack,          input logic     std_r_nak,
                            input logic     std_s_parameters,   input logic     std_s_deselect,
                            input logic     random,             input logic     error,
                            input logic     corrupt_crc,
                            input CidType   cid_type,           input NadType   nad_type,
                            output MsgType  sent);

        automatic MsgType       allowed [$] = '{};

        if (RATS) begin
            allowed.push_back(MsgType_RATS);
        end
        if (PPS) begin
            allowed.push_back(MsgType_PPS);
        end
        if (std_i_block) begin
            allowed.push_back(MsgType_I);
        end
        if (std_i_block_chaining) begin
            allowed.push_back(MsgType_I_CHAINING);
        end
        if (std_r_ack) begin
            allowed.push_back(MsgType_ACK);
        end
        if (std_r_nak) begin
            allowed.push_back(MsgType_NAK);
        end
        if (std_s_parameters) begin
            allowed.push_back(MsgType_PARAMETERS);
        end
        if (std_s_deselect) begin
            allowed.push_back(MsgType_DESELECT);
        end
        if (random) begin
            allowed.push_back(MsgType_RANDOM);
        end
        if (error) begin
            allowed.push_back(MsgType_ERROR);
        end
        if (corrupt_crc) begin
            allowed.push_back(MsgType_CORRUPTS_CRC);
        end

        std::randomize(sent) with {sent inside {allowed};};

        if ((sent == MsgType_ERROR) || (sent == MsgType_CORRUPTS_CRC)) begin
            if (sent == MsgType_ERROR) begin
                send_frame_add_error    = 1'b1;
                //$display("Setting send_frame_add_error for next message");
            end
            else begin
                send_frame_crc_error    = 1'b1;
                //$display("Setting send_frame_crc_error for next message");
            end

            // recursive call, all options enabled except error / corrupt_crc
            send_msg(.RATS              (1'b1),     .PPS                    (1'b1),
                     .std_i_block       (1'b1),     .std_i_block_chaining   (1'b1),
                     .std_r_ack         (1'b1),     .std_r_nak              (1'b1),
                     .std_s_parameters  (1'b1),     .std_s_deselect         (1'b1),
                     .random            (1'b1),     .error                  (1'b0),
                     .corrupt_crc       (1'b0),
                     .cid_type          (cid_type), .nad_type               (nad_type),
                     .sent              (sent));

            send_frame_add_error    = 1'b0;
            send_frame_crc_error    = 1'b0;

            return;
        end

        //$display("sending %s with cid_type %s, nad_type %s", sent.name, cid_type.name, nad_type.name);

        case (sent)
            MsgType_RATS:           send_rats($urandom_range(15), cid_type);
            MsgType_PPS:            send_pps(cid_type, $urandom_range(1), 0, 0);
            MsgType_I:              send_std_i_block(cid_type, nad_type, 1'b0, frame_generator_pkg::generate_byte_queue($urandom_range(10)));
            MsgType_I_CHAINING:     send_std_i_block(cid_type, nad_type, 1'b1, frame_generator_pkg::generate_byte_queue($urandom_range(10)));
            MsgType_ACK:            send_std_r_ack(cid_type);
            MsgType_NAK:            send_std_r_nak(cid_type);
            MsgType_PARAMETERS:     send_std_s_parameters(cid_type, frame_generator_pkg::generate_byte_queue($urandom_range(10)));
            MsgType_DESELECT:       send_std_s_deselect(cid_type);
            MsgType_RANDOM:         send_random;
        endcase
    endtask

    task recv_frame (output logic [7:0] data [$]);
        // max Tx is PCB + CID + INF = 2 + INF (CRC is added in the part3 block)
        // max INF depends on what is sent by the app_tx_iface so we limit that to
        // 12 bytes -> 14 bytes MAX that we expect to receive here.
        // each Tx byte takes ~12 ticks, so 12*14 = 168 ticks
        // + some delay before we start sending and a bit of wiggle room
        tx_sink.wait_for_rx_complete(256);

        data = tx_sink.get_and_clear_received_queue();

        //$display("recv: %p", data);

        if (data.size) begin
            last_received = data;
        end
    endtask

    task check_no_reply;
        automatic logic [7:0] data [$];

        //$display("checking no reply");
        // assume Rx starts within 32 clock ticks
        repeat (32) @(posedge clk) begin end

        data = tx_sink.get_and_clear_received_queue();

        verifyNoReply: assert (data.size == 0) else $error("Received reply when none expected %p", data);
    endtask

    task check_not_forwarded_to_app;
        // make sure nothing is in the received queue for the app
        automatic logic [7:0]   data [$]        = app_rx_sink.get_and_clear_received_queue();
        notForwardedToApp: assert (data.size == 0)
                           else $fatal(0,"Data was forwarded to the app when not expected, got %p", data);
    endtask

    task verify_ats;
        automatic logic [7:0] data [$];
        recv_frame(data);

        // we expect an ATS of 1 byte (TL) which is the length field and so should be 1
        verifyATS: assert ((data.size == 1) &&
                           (data[0] == 1)) else $error("ATS not as expected %p", data);
    endtask

    task verify_ppsr;
        automatic logic [7:0] data [$];
        recv_frame(data);

        // we expect a PPS relpy of 1 byte (PPS)
        verifyPPSR: assert ((data.size == 1) &&
                            (data[0] == {4'b1101, picc_cid}))
                else $error("PPS reply not as expected %p", data);
    endtask

    task verify_std_r_ack (logic expect_cid);
        automatic logic [7:0] data [$];
        automatic logic [7:0] expected [$];

        recv_frame(data);

        // prologue
        expected = '{{4'b1010, expect_cid, 2'b01, picc_block_num}};
        if (expect_cid) begin
            expected.push_back({power, 2'b00, picc_cid});
        end

        verifyRACK: assert (data == expected)
                    else $error("Expecting R(ACK) %p, got %p", expected, data);

        // ISO/IEC 14443-4:2016 section 7.5.4, Rule B
        // When an I-block or an R(ACK) block with a block number equal to the current block number
        // is received, the PCD shall toggle the current block number for that PICC before optionally
        // sending a block.
        if (picc_block_num == pcd_block_num) begin
            pcd_block_num = !pcd_block_num;
            //$display("TB: recv R(ACK) with our block num, toggling pcd_block_num %d", pcd_block_num);
        end
    endtask

    task verify_std_s_deselect (logic expect_cid);
        automatic logic [7:0] data [$];
        automatic logic [7:0] expected [$];

        // rx_deselect should assert after we finish receiving this frame
        // we have asserts at the bottom of this file that check it only asserts when
        // expected, and that it doesn't assert during the Tx frame, and that it definitely
        // does assert when it's expected
        expect_rx_deselect = 1'b1;
        recv_frame(data);
        repeat (5) @(posedge clk) begin end
        expect_rx_deselect = 1'b0;

        // prologue
        expected = '{{4'b1100, expect_cid, 3'b010}};
        if (expect_cid) begin
            expected.push_back({power, 2'b00, picc_cid});
        end

        verifyDeselect: assert (data == expected)
                        else $error("Expecting S(DESELECT) %p, got %p", expected, data);
    endtask

    task verify_std_i_block(logic expect_cid);
        automatic logic [7:0] data [$];
        automatic logic [7:0] expected [$];

        recv_frame(data);

        // prologue
        expected = '{{4'b0000, expect_cid, 2'b01, picc_block_num}};
        if (expect_cid) begin
            expected.push_back({power, 2'b00, picc_cid});
        end

        // INF
        foreach (app_last_send[i]) begin
            expected.push_back(app_last_send[i]);
        end

        //$display("verify_std_i_block received: %p", data);

        verifyParameters: assert (data == expected)
                          else $error("Expecting I-block %p, got %p", expected, data);

        // ISO/IEC 14443-4:2016 section 7.5.4, Rule B
        // When an I-block or an R(ACK) block with a block number equal to the current block number
        // is received, the PCD shall toggle the current block number for that PICC before optionally
        // sending a block.
        if (picc_block_num == pcd_block_num) begin
            pcd_block_num = !pcd_block_num;
            //$display("TB: recv STD I-block with our block num, toggling pcd_block_num %d", pcd_block_num);
        end
    endtask

    task verify_repeat_last;
        automatic logic [7:0] data [$];
        automatic logic [7:0] expected [$] = last_received;

        recv_frame(data);

        verifyRepeatLast: assert (data == expected)
                          else $error("Expected a repeat of the last frame %p, got %p", expected, data);

        // ISO/IEC 14443-4:2016 section 7.5.4, Rule B
        // When an I-block or an R(ACK) block with a block number equal to the current block number
        // is received, the PCD shall toggle the current block number for that PICC before optionally
        // sending a block.
        if ((data.size != 0) &&
            ((data[0] ==? {7'b1010x01, pcd_block_num}) ||           // R(ACK) with/without CID
             (data[0] ==? {7'b000xxx1, pcd_block_num}))) begin      // I-block with/without chaining,cid,nad
            pcd_block_num = !pcd_block_num;
            //$display("TB: recv R(ACK)/STD I-Block with our block num, toggling pcd_block_num %d", pcd_block_num);
        end
    endtask

    task verify_reply(MsgType msg, logic expect_cid);
        case (msg)
            MsgType_RATS:           verify_ats;
            MsgType_PPS:            verify_ppsr;
            MsgType_I:              verify_std_i_block(expect_cid);
            MsgType_I_CHAINING:     check_no_reply;
            MsgType_ACK:            check_no_reply;                 // assuming pcd_block_num not toggled first
            MsgType_NAK:            verify_std_r_ack(expect_cid);   // assuming pcd_block_num not toggled first
            MsgType_PARAMETERS:     check_no_reply;
            MsgType_DESELECT:       verify_std_s_deselect(expect_cid);
            default:                $error("replies to %s not supported here", msg.name);
        endcase
    endtask

    task send_app_reply(logic [7:0] inf [$]);
        // cache it for use with app_resend_last and verify_std_i_block
        app_last_send = inf;

        // send the reply
        //$display("send_app_reply %p", inf);
        app_tx_source.send_frame(inf, 0, 256);
    endtask

    task app_verify_rx_data(logic [7:0] expected_inf [$], logic expect_error=1'b0);
        automatic logic [7:0]   data [$];
        automatic logic         error;

        // data should have finished sending by the time this is called
        // since send_frame is blocking, so just a short wait to make sure.
        app_rx_sink.wait_for_idle(16);

        data    = app_rx_sink.get_and_clear_received_queue();
        error   = app_rx_sink.get_error_detected();

        checkError: assert (expect_error == error) else $error("App error state %b not as expected %b", error, expect_error);

        if (!expect_error) begin: noExpectError
            //$display("app received: %p, note: last two bytes are CRC of whole message", data);

            // drop the CRC - there's no need to check the CRC in the app, since
            // the DUT inserts an error if the rx_crc_ok signal is not OK
            void'(data.pop_back);
            void'(data.pop_back);

            appVerifyRxData: assert (expected_inf == data) else $error("App received %p expected %p", data, expected_inf);
        end
    endtask

    task app_verify_no_data_or_error;
        automatic logic [7:0]   app_rx_data [$];
        automatic logic         app_rx_error;

        // short delay to let anything that's going to come in come in.
        // the send call is blocking, so we shouldn't need to wait at all
        repeat (16) @(posedge clk) begin end
        app_rx_data     = app_rx_sink.get_and_clear_received_queue();
        app_rx_error    = app_rx_sink.get_error_detected();

        noDataOrAnError:
        assert ((app_rx_data.size == 0) || app_rx_error)
            else $error("Expecting app rx timeout or error, got %p valid", app_rx_data);
    endtask

    task goto_state_expect_rats;
        tag_active = 1'b1;  // this gets deasserted in send_frame
    endtask

    task goto_state_pps_allowed(CidType cid_type);
        goto_state_expect_rats;
        send_rats($urandom, cid_type);
        verify_ats;
    endtask

    task goto_state_others(CidType cid_type);
        goto_state_pps_allowed(cid_type);
        send_pps(CID_CURRENT, 1'($urandom_range(1)), 0, 0);
        verify_ppsr;
    endtask

    task goto_state(State state, CidType cid_type);
        case (state)
            State_EXPECT_RATS:  goto_state_expect_rats;
            State_PPS_ALLOWED:  goto_state_pps_allowed(cid_type);
            State_OTHERS:       goto_state_others(cid_type);
        endcase
    endtask

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------
    localparam int NUM_LOOPS = 1000;
    initial begin
        rx_source.initialise;
        tx_sink.initialise;
        app_rx_sink.initialise;
        app_tx_source.initialise;

        tx_sink.enable_expected_checking(1'b0);
        tx_sink.enable_receive_queue(1'b1);
        app_rx_sink.enable_expected_checking(1'b0);
        app_rx_sink.enable_receive_queue(1'b1);

        power                       = 2'b00;
        tag_active                  = 1'b0;
        rx_crc_ok                   = 1'b0;

        expect_rx_rats              = 1'b0;
        expect_rx_deselect          = 1'b0;
        expect_app_resend_last      = 1'b0;

        send_frame_add_error        = 1'b0;
        send_frame_crc_error        = 1'b0;
        send_frame_randomise_power  = 1'b1; // randomize power on each send by default

        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // we have 3 states:
        //  1) expecting RATS and nothing else, this is the case when tag_active is asserted
        //  2) expecting PPS or anything except RATS, this is the case immediately after RATS has been sent
        //  3) expecting anything except RATS or PPS, this is the case after RATS and one more message has been sent

        // 1a) Test State_EXPECT_RATS + RATS -> ATS
        $display("Testing State_EXPECT_RATS + valid RATS -> ATS");
        repeat (NUM_LOOPS) begin
            goto_state_expect_rats;
            // ISO/IEC 14443-4:2016 section 5.1
            // FSDI D-F is RFU, the PICC should interpret those values as C.
            //                  we currently ignore FSDI, so test all values.
            // CID = 15 is RFU, the PICC shall not respond and shall enter IDLE state
            //                   or HALT state as specified in ISO/IEC 14443-3:2016,
            send_rats($urandom, CID_RANDOM);
            verify_ats;
        end

        // 1b) Test State_EXPECT_RATS + invalid RATS
        $display("Testing State_EXPECT_RATS + invalid RATS");
        repeat (NUM_LOOPS) begin
            goto_state_expect_rats;
            // ISO/IEC 14443-4:2016 section 5.1
            // CID = 15 is RFU, the PICC shall not respond and shall enter IDLE state
            //                   or HALT state as specified in ISO/IEC 14443-3:2016,
            send_rats($urandom, CID_15);
            check_no_reply;
        end

        // 1c) Test State_EXPECT_RATS + anything else
        $display("Testing State_EXPECT_RATS + others");
        repeat (NUM_LOOPS) begin
            automatic MsgType last_sent;
            goto_state_expect_rats;

            // send any message other than RATS, send with or without a random CID / NAD
            send_msg(.RATS              (1'b0),                 .PPS                    (1'b1),
                     .std_i_block       (1'b1),                 .std_i_block_chaining   (1'b1),
                     .std_r_ack         (1'b1),                 .std_r_nak              (1'b1),
                     .std_s_parameters  (1'b1),                 .std_s_deselect         (1'b1),
                     .random            (1'b1),                 .error                  (1'b1),
                     .corrupt_crc       (1'b1),
                     .cid_type          (CID_RANDOM_WITH_15),   .nad_type               (NAD_RANDOM),
                     .sent              (last_sent));
            check_no_reply;
        end

        // end of test 1), check nothing has been forwarded to the APP
        check_not_forwarded_to_app;

        // 2a) Test State_PPS_ALLOWED + PPS (no P1) -> PPSR
        $display("Testing State_PPS_ALLOWED + valid PPS (no P1) -> PPSR");
        repeat (NUM_LOOPS) begin
            goto_state(State_PPS_ALLOWED, CID_RANDOM);
            send_pps(CID_CURRENT, 0, 0, 0);
            verify_ppsr;
            // send a second PPS and check we don't respond
            send_pps(CID_CURRENT, 1'($urandom), 0, 0);
            check_no_reply;
        end

        // 2b) Test State_PPS_ALLOWED + PPS (with P1) -> PPSR
        $display("Testing State_PPS_ALLOWED + valid PPS (with P1) -> PPSR");
        repeat (NUM_LOOPS) begin
            goto_state(State_PPS_ALLOWED, CID_RANDOM);
            send_pps(CID_CURRENT, 1, 0, 0);
            verify_ppsr;
            // send a second PPS and check we don't respond
            send_pps(CID_CURRENT, 1'($urandom), 0, 0);
            check_no_reply;
        end

        // 2c) Test State_PPS_ALLOWED + invalid PPS (cid not us) -> no reply
        $display("Testing State_PPS_ALLOWED + invalid PPS (cid not us) -> no reply");
        repeat (NUM_LOOPS) begin
            goto_state(State_PPS_ALLOWED, CID_RANDOM);
            send_pps(CID_RANDOM_NOT_CURRENT, 1'($urandom), 0, 0);
            check_no_reply;
            // send a second PPS (to us this time) and check we don't respond
            send_pps(CID_CURRENT, 1'($urandom), 0, 0);
            check_no_reply;
        end

        // 2d) Test State_PPS_ALLOWED + invalid PPS (dividers) -> no reply
        $display("Testing State_PPS_ALLOWED + invalid PPS (dividers) -> no reply");
        repeat (NUM_LOOPS) begin
            goto_state(State_PPS_ALLOWED, CID_RANDOM);
            send_pps(CID_CURRENT, 1'b1, 2'($urandom_range(1,3)), 2'($urandom_range(1,3)));
            check_no_reply;
            // send a second PPS (valid this time) and check we don't respond
            send_pps(CID_CURRENT, 1'($urandom), 0, 0);
            check_no_reply;
        end

        // 2e) Test State_PPS_ALLOWED + invalid PPS (crc) -> no reply
        $display("Testing State_PPS_ALLOWED + invalid PPS (crc) -> no reply");
        repeat (NUM_LOOPS) begin
            goto_state(State_PPS_ALLOWED, CID_RANDOM);
            send_frame_crc_error = 1'b1;
            send_pps(CID_CURRENT, 1'($urandom), 0, 0);
            send_frame_crc_error = 1'b0;
            check_no_reply;
            // send a second PPS (valid this time) and check we don't respond
            send_pps(CID_CURRENT, 1'($urandom), 0, 0);
            check_no_reply;
        end

        // 2f) Test State_PPS_ALLOWED + invalid PPS (error) -> no reply
        $display("Testing State_PPS_ALLOWED + invalid PPS (error) -> no reply");
        repeat (NUM_LOOPS) begin
            goto_state(State_PPS_ALLOWED, CID_RANDOM);
            send_frame_add_error = 1'b1;
            send_pps(CID_CURRENT, 1'($urandom), 0, 0);
            send_frame_add_error = 1'b0;
            check_no_reply;
            // send a second PPS (valid this time) and check we don't respond
            send_pps(CID_CURRENT, 1'($urandom), 0, 0);
            check_no_reply;
        end

        // 2g) Test State_PPS_ALLOWED + RATS -> no reply
        $display("Testing State_PPS_ALLOWED + RATS -> no reply");
        repeat (NUM_LOOPS) begin: PPSAllowedPlusRATS
            automatic logic [3:0] old_cid;
            goto_state(State_PPS_ALLOWED, CID_RANDOM);

            // cache our current CID
            old_cid = picc_cid;

            // send a RATS any CID (!= 15)
            send_rats ($urandom_range(15), CID_RANDOM);
            check_no_reply;

            // check that we don't think the CID has changed
            tbCIDNotChanged:
            assert (picc_cid == old_cid) else $error("The TB's CID has changed on second RATS");

            // check that the DUT's CID hasn't changed
            dutCIDNotChanged:
            assert (dut.our_cid == old_cid) else $error("The DUT's CID has changed on second RATS");
        end

        // end of test 2), check nothing has been forwarded to the APP
        check_not_forwarded_to_app;

        // Test set 3) runs multiple times
        // repeat 3 times - go to State_PPS_ALLOWED before each test
        //                - go to State_OTHERS before each test
        //                - go to State_OTHERS at the start of the loop

        begin
            typedef enum
            {
                TestType_STATE_PPS_ALLOWED_BEFORE_EACH_TEST,
                TestType_STATE_OTHERS_BEFORE_EACH_TEST,
                TestType_STATE_OTHERS_ONCE
            } TestType;

            automatic TestType tests [3] = '{TestType_STATE_PPS_ALLOWED_BEFORE_EACH_TEST,
                                             TestType_STATE_OTHERS_BEFORE_EACH_TEST,
                                             TestType_STATE_OTHERS_ONCE};

            foreach (tests[testIdx]) begin
                automatic State state                       = State_OTHERS;
                automatic logic change_state_before_test    = 1'b1;

                // for each of those tests, we repeat twice more
                //      - PCD assigns random CID (not 0), messages are sent with CID
                //      - PCD assigns CID=0, messages are sent without CID
                automatic CidType cid_types [2]             = '{CID_RANDOM_NOT_ZERO, CID_NONE};

                if (tests[testIdx] == TestType_STATE_PPS_ALLOWED_BEFORE_EACH_TEST) begin
                    state = State_PPS_ALLOWED;
                end

                foreach (cid_types[cid_idx]) begin
                    automatic CidType   set_cid_type;
                    automatic CidType   send_cid_type;
                    automatic logic     expect_cid;

                    // when setting CID, use specified CID type
                    set_cid_type    = cid_types[cid_idx];
                    // when sending messages use the current CID if we have one, or CID_NONE if we don't
                    send_cid_type   = (cid_types[cid_idx] == CID_NONE) ? CID_NONE
                                                                       : CID_CURRENT;
                    // do we expect a CID in the reply?
                    expect_cid      = cid_types[cid_idx] != CID_NONE;

                    $display("Running test: %s with cid_type %s", tests[testIdx].name, cid_types[cid_idx].name);

                    // if we are in the TestType_STATE_OTHERS_ONCE
                    // then goto State_OTHERS once here
                    if (tests[testIdx] == TestType_STATE_OTHERS_ONCE) begin
                        goto_state(State_OTHERS, set_cid_type);
                        change_state_before_test = 1'b0;
                    end

                    // 3a) RATS is ignored
                    $display("  Testing RATS is ignored");
                    repeat (NUM_LOOPS) begin
                        if (change_state_before_test) begin
                            goto_state(state, set_cid_type);
                        end

                        // send a RATS any CID (!= 15)
                        send_rats ($urandom_range(15), CID_RANDOM);
                        check_no_reply;
                    end
                    check_not_forwarded_to_app;

                    // 3b) PPS is ignored (only in State_OTHERS)
                    if (state == State_OTHERS) begin
                        $display("  Testing PPS is ignored");
                        repeat (NUM_LOOPS) begin
                            if (change_state_before_test) begin
                                goto_state(state, set_cid_type);
                            end

                            // send a PPS
                            send_pps(send_cid_type, 1'($urandom), 0, 0);
                            check_no_reply;
                        end
                        check_not_forwarded_to_app;
                    end

                    // 3c) Test S(PARAMETERS)
                    $display("  Testing S(PARAMETERS)");
                    repeat (NUM_LOOPS) begin
                        automatic int inf_bytes = $urandom_range(10);
                        if (change_state_before_test) begin
                            goto_state(state, set_cid_type);
                        end

                        // send S(PARAMETERS)
                        send_std_s_parameters(send_cid_type, frame_generator_pkg::generate_byte_queue(inf_bytes));
                        check_no_reply;
                    end
                    check_not_forwarded_to_app;

                    // 3d) Test S(DESELECT)
                    // note: Normally after S(DESELECT) we would require re-initialisation
                    //       but that's done in the iso14443_3a module, by changing the message
                    //       routing. Here we can just continue to send messages.
                    $display("  Testing S(DESELECT)");
                    repeat (NUM_LOOPS) begin
                        if (change_state_before_test) begin
                            goto_state(state, set_cid_type);
                        end

                        // send S(DESELECT)
                        send_std_s_deselect(send_cid_type);
                        verify_std_s_deselect(expect_cid);
                    end
                    check_not_forwarded_to_app;

                    // 3e) Test I-blocks with chaining are ignored
                    $display("  Testing I-blocks with chaining");
                    repeat (NUM_LOOPS) begin
                        automatic int inf_bytes = $urandom_range(10);
                        if (change_state_before_test) begin
                            goto_state(state, set_cid_type);
                        end

                        // send I-block witch chaining enabled
                        // we also add a NAD 50% of the time
                        // which should also mean the message is ignored.
                        send_std_i_block(send_cid_type, NAD_RANDOM, 1'b1, frame_generator_pkg::generate_byte_queue(inf_bytes));
                        check_no_reply;
                        check_not_forwarded_to_app;
                    end

                    // 3f) Test I-blocks with NADs are ignored
                    $display("  Testing I-blocks with NADs");
                    repeat (NUM_LOOPS) begin
                        automatic int inf_bytes = $urandom_range(10);
                        if (change_state_before_test) begin
                            goto_state(state, set_cid_type);
                        end

                        // send I-block without chaining but with a NAD
                        send_std_i_block(send_cid_type, NAD_PRESENT, 1'b0, frame_generator_pkg::generate_byte_queue(inf_bytes));
                        check_no_reply;
                        check_not_forwarded_to_app;
                    end

                    // 3g.i) Test valid I-blocks are forwarded to the app and the reply comes through
                    $display("  Testing valid I-blocks");
                    repeat (NUM_LOOPS) begin
                        automatic int           inf_bytes   = $urandom_range(10);
                        automatic logic [7:0]   inf [$]     = frame_generator_pkg::generate_byte_queue(inf_bytes);

                        if (change_state_before_test) begin
                            goto_state(state, set_cid_type);
                        end

                        //$display("sending I-block with inf: %p", inf);

                        // send I-block without chaining and no NAD
                        send_std_i_block(send_cid_type, NAD_NONE, 1'b0, inf);

                        // verify the data is received OK
                        verify_std_i_block(expect_cid);
                    end

                    // 3g.ii) Test I-blocks with CRC fails
                    $display("  Testing valid I-blocks with CRC fails");
                    repeat (NUM_LOOPS) begin
                        automatic int           inf_bytes   = $urandom_range(10);
                        automatic logic [7:0]   inf [$]     = frame_generator_pkg::generate_byte_queue(inf_bytes);

                        if (change_state_before_test) begin
                            goto_state(state, set_cid_type);
                        end

                        // send I-block without chaining and no NAD
                        send_frame_crc_error = 1'b1;
                        send_std_i_block(send_cid_type, NAD_NONE, 1'b0, inf);
                        send_frame_crc_error = 1'b0;

                        // check there's no reply
                        check_no_reply;
                    end

                    // 3g.iii) Test I-blocks with errors
                    $display("  Testing valid I-blocks with errors");
                    repeat (NUM_LOOPS) begin
                        automatic int           inf_bytes   = $urandom_range(10);
                        automatic logic [7:0]   inf [$]     = frame_generator_pkg::generate_byte_queue(inf_bytes);

                        if (change_state_before_test) begin
                            goto_state(state, set_cid_type);
                        end

                        // send I-block without chaining and no NAD
                        send_frame_add_error = 1'b1;
                        send_std_i_block(send_cid_type, NAD_NONE, 1'b0, inf);
                        send_frame_add_error = 1'b0;

                        // check there's no reply
                        check_no_reply;
                    end

                    // 3h) Test R(ACK) with current PCD block num are ignored
                    $display("  Testing R(ACK) with current PCD block num");
                    repeat (NUM_LOOPS) begin
                        if (change_state_before_test) begin
                            goto_state(state, set_cid_type);
                        end

                        // ISO/IEC 14443-4:2016 section 7.5.5.3 rule 13) states that
                        // When an R(ACK) block is received, if it's block number is not equal to the
                        // PICC’s current block number and the PICC is in chaining, chaining shall be
                        // continued.
                        // Since we don't support chaining, ACKs with block number != the PICC's
                        // current block number are ignored. check that this is the case here.
                        // asserting is hard because Synopsys doesn't like unnamed asserts
                        // and doesn't seem to name loops correctly. So I use a $fatal instead
                        if (pcd_block_num == dut.our_block_num) begin
                            // pcd_block_num is equal to the PICC's block num.
                            // we want to test when they are not equal
                            $fatal(0, "PCD block num == PICC block num (in the DUT)", pcd_block_num, dut.our_block_num);
                        end
                        send_std_r_ack(send_cid_type);
                        check_no_reply;
                    end
                    check_not_forwarded_to_app;

                    // 3i) Test R(NAK) with current PCD block num -> R(ACK)
                    $display("  Testing R(NAK) with current PCD block num -> R(ACK)");
                    repeat (NUM_LOOPS) begin
                        if (change_state_before_test) begin
                            goto_state(state, set_cid_type);
                        end

                        // ISO/IEC 14443-4:2016 section 7.5.5.3 rule 12) states that
                        // When an R(NAK) block is received, if it's block number is not equal
                        // to the PICC’s current block number, an R(ACK) block shall be sent.
                        // check that this is the case here.
                        if (pcd_block_num == dut.our_block_num) begin
                            // pcd_block_num is equal to the PICC's block num.
                            // we want to test when they are not equal
                            $fatal(0, "PCD block num == PICC block num (in the DUT)", pcd_block_num, dut.our_block_num);
                        end

                        send_std_r_nak(send_cid_type);
                        verify_std_r_ack(expect_cid);
                    end
                    check_not_forwarded_to_app;

                    // 3j) Test R(ACK/NAK) with toggled PCD block num -> resend last
                    $display("  Testing R(ACK/NAK) with toggled PCD block num");
                    repeat (NUM_LOOPS) begin
                        automatic MsgType       last_sent;
                        automatic MsgType       dummy;
                        automatic logic [7:0]   data        [$];

                        if (change_state_before_test) begin
                            goto_state(state, set_cid_type);
                        end

                        // first send random (valid message) I-block, R(NAK).
                        // we don't allow S(DESELECT) because that complicates rx_deselect detection
                        // and the appropriate PCD response to not receiving the S(DESELECT) reply
                        // is to resend S(DESELECT).
                        // we don't allow R(ACK) because that doesn't result in a reply
                        send_msg(.RATS              (1'b0),             .PPS                    (1'b0),
                                 .std_i_block       (1'b1),             .std_i_block_chaining   (1'b0),
                                 .std_r_ack         (1'b0),             .std_r_nak              (1'b1),
                                 .std_s_parameters  (1'b0),             .std_s_deselect         (1'b0),
                                 .random            (1'b0),             .error                  (1'b0),
                                 .corrupt_crc       (1'b0),
                                 .cid_type          (send_cid_type),    .nad_type               (NAD_NONE),
                                 .sent              (last_sent));

                        verify_reply(last_sent, expect_cid);

                        // toggle the PCD block num (fake not having received the reply)
                        pcd_block_num = !pcd_block_num;

                        // ISO/IEC 14443-4:2016 section 7.5.5.3 rule 11) states that
                        // When an R(ACK) or an R(NAK) block is received, if it's block number is equal
                        // to the PICC's current block number, the last block shall be re-transmitted.
                        // Wheras section 7.5.6.2 b) states:
                        // toggle its block number then send an R(NAK) block and expect to receive
                        // the last I-block from the PICC [rule 11].
                        // So test here that these are the same thing.
                        if (pcd_block_num != dut.our_block_num) begin
                            // pcd_block_num is not equal to the PICC's block num.
                            // we want to test when they are equal
                            $fatal(0, "PCD block num != PICC block num (in the DUT)", pcd_block_num, dut.our_block_num);
                        end

                        // if we previously had sent an I-block we expect app_resend_last to assert
                        if (last_sent == MsgType_I) begin
                            expect_app_resend_last  = 1'b1;
                        end

                        // send an R(ACK) or R(NAK)
                        // don't randomize the power signal
                        // or this beraks the verify_repeat_last checking
                        send_frame_randomise_power = 1'b0;
                        send_msg(.RATS              (1'b0),             .PPS                    (1'b0),
                                 .std_i_block       (1'b0),             .std_i_block_chaining   (1'b0),
                                 .std_r_ack         (1'b1),             .std_r_nak              (1'b1),
                                 .std_s_parameters  (1'b0),             .std_s_deselect         (1'b0),
                                 .random            (1'b0),             .error                  (1'b0),
                                 .corrupt_crc       (1'b0),
                                 .cid_type          (send_cid_type),    .nad_type               (NAD_NONE),
                                 .sent              (dummy));

                        // if it was an I-block we need to actually resend the app data
                        if (last_sent == MsgType_I) begin
                            // resend last data
                            send_app_reply(app_last_send);
                        end

                        // verify that the DUT resent it's last message
                        verify_repeat_last;

                        // go back to randomising the power signal
                        send_frame_randomise_power = 1'b1;
                    end
                    check_not_forwarded_to_app;

                    // 3k) Test errors (random invalid data, CRC fail, rx_iface.error)
                    $display("  Testing errors");
                    repeat (NUM_LOOPS) begin
                        automatic MsgType last_sent;
                        if (change_state_before_test) begin
                            goto_state(state, set_cid_type);
                        end

                        // send either a random none-valid msg, or any valid one with a CRC fail / error
                        send_msg(.RATS              (1'b0),             .PPS                    (1'b0),
                                 .std_i_block       (1'b0),             .std_i_block_chaining   (1'b0),
                                 .std_r_ack         (1'b0),             .std_r_nak              (1'b0),
                                 .std_s_parameters  (1'b0),             .std_s_deselect         (1'b0),
                                 .random            (1'b1),             .error                  (1'b1),
                                 .corrupt_crc       (1'b1),
                                 .cid_type          (send_cid_type),    .nad_type               (NAD_NONE),
                                 .sent              (last_sent));
                        app_verify_no_data_or_error;
                        check_no_reply;
                    end

                    // 3l) Test not for us
                    $display("  Testing not for us");
                    repeat (NUM_LOOPS) begin
                        automatic MsgType last_sent;
                        if (change_state_before_test) begin
                            goto_state(state, set_cid_type);
                        end

                        // send any STD block with CID not CURRENT
                        send_msg(.RATS              (1'b0),                     .PPS                    (1'b0),
                                 .std_i_block       (1'b1),                     .std_i_block_chaining   (1'b1),
                                 .std_r_ack         (1'b1),                     .std_r_nak              (1'b1),
                                 .std_s_parameters  (1'b1),                     .std_s_deselect         (1'b1),
                                 .random            (1'b0),                     .error                  (1'b0),
                                 .corrupt_crc       (1'b0),
                                 .cid_type          (CID_RANDOM_NOT_CURRENT),   .nad_type               (NAD_NONE),
                                 .sent              (last_sent));
                        check_not_forwarded_to_app;
                        check_no_reply;
                    end

                    // 3m) Test no CID (only when set_cid_type != CID_NONE)
                    if (set_cid_type != CID_NONE) begin
                        $display("  Testing no CID");
                        repeat (NUM_LOOPS) begin
                            automatic MsgType last_sent;
                            if (change_state_before_test) begin
                                goto_state(state, set_cid_type);
                            end

                            // send any STD block without a CID
                            send_msg(.RATS              (1'b0),     .PPS                    (1'b0),
                                     .std_i_block       (1'b1),     .std_i_block_chaining   (1'b1),
                                     .std_r_ack         (1'b1),     .std_r_nak              (1'b1),
                                     .std_s_parameters  (1'b1),     .std_s_deselect         (1'b1),
                                     .random            (1'b0),     .error                  (1'b0),
                                     .corrupt_crc       (1'b0),
                                     .cid_type          (CID_NONE), .nad_type               (NAD_NONE),
                                     .sent              (last_sent));
                            check_not_forwarded_to_app;
                            check_no_reply;
                        end
                    end

                    // 3n) PICC presence checks, see ISO/IEC 14443-4:2016 section 7.5.6
                    // 3n.1) Method 1 - The PCD may send and empty I-Block and expect to
                    //       receive an I-Block from the PICC.
                    // Note: We don't test this here because we've already tested I-Block
                    //       transmissions work. And while we don't explicitly test empty
                    //       I-Blocks the size of the INF field is random and includes 0 in it's range.

                    // 3n.2) Method 2 - Before the first I-block exchange, the PCD may send an
                    //       R(NAK) block (with block number 0) and expect to receive an R(ACK)
                    //       (with block number 1) block from the PICC [rule 12].
                    // Note: We can only do this if change_state_before_test is set, otherwise
                    //       there have been I-Block exchanges already
                    // Note: We do test this here because it explicitly gives block numbers.
                    //       While we have already tested R(NAK) -> R(ACK) as the first messages
                    //       after RATS, this ensures that the block numbers work as expected.
                    if (change_state_before_test) begin
                        $display("  Testing PICC presence check Method 2 (before first I-Block exchange");
                        repeat (NUM_LOOPS) begin
                            goto_state(state, set_cid_type);

                            // send an R(NAK) with block number 0
                            pcd_block_num = 1'b0;
                            send_std_r_nak(send_cid_type);

                            // expect to receive with picc block number 1
                            picc_block_num = 1'b1;
                            verify_std_r_ack(expect_cid);
                        end
                    end

                    // 3n.2a) Method 2 - After the first I-block exchange, the PCD may either
                    //        a) send an R(NAK) block (with current block number) and expect
                    //           to receive an R(ACK) block from the PICC [rule 12].
                    // Note: we don't test this here, we already know that an R(NAK) with the correct
                    //       block number will cause an R(ACK) to be received.

                    // 3n.2b) Method 2 - or
                    //        b) toggle its block number then send an R(NAK) block and expect to
                    //           receive the last I-block from the PICC [rule 11].
                    // Note: again we don't test this here, as we know that this works
                end
            end
        end

        // 4) ISO/IEC 14443-4:2016 section 7.5.5.1
        // Rule 1) The first block shall be sent by the PCD
        $display("Testing Rule 1) The first block shall be sent by the PCD");
        // clear any old data
        void'(tx_sink.get_and_clear_received_queue());
        // reset for 5 ticks
        rst_n <= 1'b0;
        repeat (5) @(posedge clk) begin end
        rst_n <= 1'b1;
        repeat (5) @(posedge clk) begin end

        // wait a while and check the PICC doesn't transmit anything
        repeat (5000) @(posedge clk) begin end
        // check that nothing was received
        begin: testPiccNoTxFirst
            automatic logic [7:0] data [$] = tx_sink.get_and_clear_received_queue();
            piccNoTxFirst: assert (data.size() == 0) else $error("PICC transmitted first");
        end

        // Rule 2) When an I-Block with chaining is received, the block shall be acknowledged
        // by an R(ACK) block.
        // The DUT currently does not support chaining. So we don't test this.

        // Rule 3) S-Blocks are only used in pairs. An S(...) request block shall always be followed
        // by an S(...) response block.
        // We test this by making sure the reply to S(DESELECT) is S(DESELECT)
        // The DUT does not support S(PARAMETERS) and as per ISO/IEC 14443-4:2016 section 9
        // the DUT remains mute upon receiving S(PARAMETERS).

        // PCD rules 4) - 8) do not apply to us.

        // Rule 9) The PICC is allowed to send an S(WTX) block instead of an I-block or an R(ACK) block.
        // The PICC never sends S(WTX) as of yet.

        // Rule 10) When an I-Block not indicating chaining is received, the block shall be acknowledged
        // with an I-Block. This is tested in test 3)
        // Note: If the I-Block received is empty then the mandatory I-Block sent can either be empty
        // or can contain application specific information.

        // Rule 11) When an R(ACK) or an R(NAK) block is received, if it's block number is equal
        // to the PICC's current block number, the last block shall be re-transmitted.
        // This is tested in test 3)

        // Rule 12) When an R(NAK) block is received, if it's block number is not equal to the
        // PICC’s current block number, an R(ACK) block shall be sent.
        // This is tested in test 3)

        // Rule 13) When an R(ACK) block is received, if it's block number is not equal to the
        // PICC’s current block number and the PICC is in chaining, chaining shall be continued.
        // The DUT doesn't support chaining, so R(ACKs) with the PICC's current block number are
        // ignored

        // TODO
        //  run through all examples in appendix B
        //      pay attention to block num

        repeat (5) @(posedge clk) begin end
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

    // check signals in reset
    inReset:
    assert property (
        @(posedge clk)
        !rst_n |-> (!rx_rats && !rx_deselect && !app_resend_last))
        else $error("signals in reset not as expected");

    // tx_append_crc should always be set
    txAppendCRC:
    assert property (@(posedge clk) tx_append_crc)
        else $error("tx_append_crc should always be set");

    // check rx_rats only asserts when expected, we check it deasserts by
    // making sure it is not asserted after we finish sending each frame
    rxRatsOnlyWhenExpected:
    assert property (
        @(posedge clk)
        $rose(rx_rats) |-> expect_rx_rats)
        else $error("rx_rats asserted when not expected");

    // check app_resend_last only asserts when expected
    appResendLastOnlyWhenExpected:
    assert property (
        @(posedge clk)
        $rose(app_resend_last) |-> expect_app_resend_last)
        else $error("app_resend_last asserted when not expected");

    // check rx_deselect only asserts when expected
    rxDeselectOnlyWhenExpected:
    assert property (
        @(posedge clk)
        $rose(rx_deselect) |-> expect_rx_deselect)
        else $error("rx_deselect asserted when not expected");

    // check rx_deselect asserts when expected
    rxDeselectWhenExpected:
    assert property (
        @(posedge clk)
        $rose(expect_rx_deselect) |=> expect_rx_deselect throughout rx_deselect[->1])
        else $error("rx_deselect didn't assert when expected");

    // check rx_deselect only asserts for one tick at a time
    rxDeselectOneTick:
    assert property (
        @(posedge clk)
        $rose(rx_deselect) |=> $fell(rx_deselect))
        else $error("rx_deselect asserted for more than one tick at a time");

    // check rx_deselect does not asserts in the middle of a frame (rx / tx)
    rxDeselectDuringTx:
    assert property (
        @(posedge clk)
        rx_deselect |-> !tx_iface.data_valid)
        else $error("rx_deselect asserted when tx_iface.data_valid was asserted");

    // check app_resend_last only asserts for one tick at a time
    appResendLastOneTick:
    assert property (
        @(posedge clk)
        $rose(app_resend_last) |=> $fell(app_resend_last))
        else $error("app_resend_last asserted for more than one tick at a time");

    // check tx_iface.data_bits is always 0
    dataBitsAlways0:
    assert property (
        @(posedge clk)
        (tx_iface.data_bits == 0))
        else $error("tx_iface.data_bits != 0");

endmodule
