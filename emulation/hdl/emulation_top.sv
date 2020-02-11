/***********************************************************************
        File: emulation_top.sv
 Description: Top level module for the emulation project
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

module emulation_top
(
    input                   CLOCK_50,
    input           [0:0]   KEY,
    input                   PAUSE,  // our pause input (active high)    - GPIO_0[0]
    output logic            TX,     // our Tx output                    - GPIO_0[1]
    output logic    [8:0]   LEDG,
    output logic    [17:0]  LEDR,
    output logic    [6:0]   HEX4,
    output logic    [6:0]   HEX5,
    output logic    [6:0]   HEX6
);

    // ========================================================================
    // Aliases
    // ========================================================================

    // KEY[0] is active low rst
    logic rst_n;
    assign rst_n = KEY[0];

    // GPIO_0[0] is pause
    logic pause_n;
    assign pause_n = !PAUSE;

    // GPIO_0[1] is TX

    // ========================================================================
    // PLLs and clock control
    // ========================================================================

    // The 13.56 MHz clock. We pass this through a clock control block,
    // and use that for the ISO14443 system
    // note it's not actually 13.56MHz, closest I can get is 13.54MHz
    logic clk_13p56_tmp;
    logic clk_13p56_tmp_locked;
    pll1 pll1_inst
    (
        .areset     (!rst_n),
        .inclk0     (CLOCK_50),
        .c0         (clk_13p56_tmp),
        .locked     (clk_13p56_tmp_locked)
    );

    logic clk_13p56_en;
    logic clk_13p56;
    clkctrl clkctrl_inst
    (
        .ena        (clk_13p56_en),
        .inclk      (clk_13p56_tmp),
        .outclk     (clk_13p56)
    );

    // ========================================================================
    // Synchronise the pause_n signal to the 13.56MHz clk
    // for internal purposes only
    // ========================================================================

    logic pause_n_tmp;
    logic pause_n_synchronised_internal;

    // note: we use clk_13p56_tmp so that we don't get stuck when the clock is stopped
    always_ff @(posedge clk_13p56_tmp, negedge rst_n) begin
        if (!rst_n) begin
            pause_n_tmp                     <= 1;
            pause_n_synchronised_internal   <= 1;
        end
        else begin
            pause_n_synchronised_internal   <= pause_n_tmp;
            pause_n_tmp                     <= pause_n;
        end
    end

    // ========================================================================
    // 13.56MHz clock and reset control
    // ========================================================================

    // if pause_n is low for too long then we assume there's no field and put the
    // DUT in reset. I use two bit times = 256 ticks for this.
    logic [7:0] counter;
    logic       iso14443_rst_n;

    // note: we use the clk_13p56_tmp here, so we can continue working when the
    // clk is disabled.
    // The clkcltrl block ena signal must be synchronised to the clk it is
    // enabling, as such we can't use the 50MHz clk here.
    always_ff @(posedge clk_13p56_tmp, negedge rst_n) begin
        if (!rst_n) begin
            clk_13p56_en    <= 0;
            iso14443_rst_n  <= 0;
            counter         <= 0;
        end
        else begin
            // enable the clk when pause_n_synchronised_internal is high
            // disable it when it is low
            clk_13p56_en <= pause_n_synchronised_internal;

            if (pause_n_synchronised_internal == 0) begin
                // in a pause, or there's no field available
                if (counter == 255) begin
                    // counter maxed out
                end
                else begin
                    counter <= counter + 1'd1;
                end
            end
            else begin
                counter <= 0;
            end

            // if our 13.56MHz clock is not locked, then put the ISO14443 in reset
            // or if we've maxed out counter out
            if ((counter == 255) || !clk_13p56_tmp_locked) begin
                iso14443_rst_n <= 0;
            end
            else begin
                iso14443_rst_n <= 1;
            end
        end
    end

    // ========================================================================
    // The ISO14443 system
    // ========================================================================

    /* iso14443a_top
    #(
        .EMULATOR_PROJECT   (1)
    )
    dut
    (
        .clk        (clk_13p56),
        .rst_n      (iso14443_rst_n),

        .pause_n    (pause_n)
    ); */

    logic iso14443_rst_n_synchronised;
    active_low_reset_synchroniser reset_synchroniser
    (
        .clk        (clk_13p56),
        .rst_n_in   (iso14443_rst_n),
        .rst_n_out  (iso14443_rst_n_synchronised)
    );

    logic pause_n_synchronised;
    active_low_reset_synchroniser pause_n_synchroniser
    (
        .clk        (clk_13p56),
        .rst_n_in   (pause_n),
        .rst_n_out  (pause_n_synchronised)
    );

    logic       rx_soc;
    logic       rx_eoc;
    logic [7:0] rx_data;
    logic [2:0] rx_data_bits;
    logic       rx_data_valid;
    logic       rx_sequence_error;
    logic       rx_parity_error;
    logic       rx_last_bit;

    logic       fdt_trigger;

    logic [7:0] tx_data;
    logic [2:0] tx_data_bits;
    logic       tx_ready_to_send;
    logic       tx_req;

    rx
    #(
        .EMULATOR_PROJECT   (1)
    )
    rx_inst
    (
        .clk                    (clk_13p56),
        .rst_n                  (iso14443_rst_n_synchronised),
        .pause_n_synchronised   (pause_n_synchronised),

        .soc                    (rx_soc),
        .eoc                    (rx_eoc),
        .data                   (rx_data),
        .data_bits              (rx_data_bits),
        .data_valid             (rx_data_valid),
        .sequence_error         (rx_sequence_error),
        .parity_error           (rx_parity_error),
        .last_bit               (rx_last_bit)
    );

    tx tx_inst
    (
        .clk                    (clk_13p56),
        .rst_n                  (iso14443_rst_n_synchronised),
        .fdt_trigger            (fdt_trigger),
        .data                   (tx_data),
        .data_bits              (tx_data_bits),
        .ready_to_send          (tx_ready_to_send),
        .req                    (tx_req),
        .tx                     (TX)
    );

    // TIMING_ADJUST is not as important here as it is in the ASIC project.
    // the reason for this is that here we don't care about collisions with other
    // cards. So the exact offset between Rx and Tx isn't important.
    localparam int TIMING_ADJUST = 0;

    fdt
    #(
        .TIMING_ADJUST  (TIMING_ADJUST)
    )
    fdt_inst
    (
        .clk                    (clk_13p56),
        .rst_n                  (iso14443_rst_n_synchronised),
        .pause_n_synchronised   (pause_n_synchronised),
        .last_rx_bit            (rx_last_bit),
        .trigger                (fdt_trigger)
    );

    // loopback logic
    // this is really basic, it waits for us to receive valid rx data
    // then tells the tx module that we are ready to send that.
    // Once that byte has been sent we stop sending more until the next frame.
    // So it only loops back the last byte received per frame
    // we don't check for SOC, EOC, errors, etc..
    always @(posedge clk_13p56, negedge iso14443_rst_n_synchronised) begin
        if (!iso14443_rst_n_synchronised) begin
            tx_ready_to_send <= 1'b0;
        end
        else begin
            // on rx_data_valid we set the tx data / bits and rts signals
            if (rx_data_valid) begin
                tx_data             <= rx_data;
                tx_data_bits        <= rx_data_bits;
                tx_ready_to_send    <= 1'b1;
            end

            // when the tx module asks for more data, deassert the rts signal
            if (tx_req) begin
                tx_ready_to_send    <= 1'b0;
            end
        end
    end

    // ========================================================================
    // Debug output
    // ========================================================================

    logic [7:0] lastData;
    logic [3:0] lastDataBits;
    logic [3:0] lastFrameDataBytes;
    logic       lastFrameSeenSoc;
    logic       lastFrameSeenEoc;
    logic       lastFrameSeenParity;
    logic       lastFrameSeenSeqErr;
    logic       lastFrameSeenDataValid;

    always_ff @(posedge clk_13p56, negedge rst_n) begin
        if (!rst_n) begin
            lastData                <= 0;
            lastDataBits            <= 0;
            lastFrameDataBytes      <= 0;
            lastFrameSeenSoc        <= 0;
            lastFrameSeenEoc        <= 0;
            lastFrameSeenParity     <= 0;
            lastFrameSeenSeqErr     <= 0;
            lastFrameSeenDataValid  <= 0;
        end
        else begin
            if (rx_soc) begin
                // seen SOC, clear flags
                lastFrameDataBytes      <= 0;
                lastFrameSeenEoc        <= 0;
                lastFrameSeenParity     <= 0;
                lastFrameSeenSeqErr     <= 0;
                lastFrameSeenDataValid  <= 0;

                // set the SOC flag
                lastFrameSeenSoc        <= 1;
            end

            if (rx_eoc) begin
                // seen EOC, clear SOC flag
                lastFrameSeenSoc        <= 0;

                // set the EOC flag
                lastFrameSeenEoc        <= 1;
            end

            if (rx_parity_error) begin
                lastFrameSeenParity     <= 1;
            end

            if (rx_sequence_error) begin
                lastFrameSeenSeqErr     <= 1;
            end

            if (rx_data_valid) begin
                lastFrameDataBytes      <= lastFrameDataBytes + 1'd1;
                lastFrameSeenDataValid  <= 1;
                lastData                <= rx_data;
                lastDataBits            <= (rx_data_bits == 0) ? 4'd8 : rx_data_bits;
            end
        end
    end

    assign LEDG[0]  = !rst_n;
    assign LEDG[1] = iso14443_rst_n;
    assign LEDG[2] = clk_13p56_tmp_locked;
    assign LEDG[3] = clk_13p56_en;
    assign LEDG[4] = pause_n;
    assign LEDG[5] = 0;
    assign LEDG[6] = 0;
    assign LEDG[7] = 0;
    assign LEDG[8] = 0;

    assign LEDR[0] = lastFrameSeenEoc;
    assign LEDR[1] = lastFrameSeenSeqErr;
    assign LEDR[2] = lastFrameSeenParity;
    assign LEDR[3] = lastFrameSeenDataValid;
    assign LEDR[4] = lastFrameSeenSoc;
    assign LEDR[17:5] = 0;

    seven_seg_hex seven_seg_inst_0
    (
        .clk        (clk_13p56_tmp),
        .rst_n      (rst_n),
        .en         (1'b1),
        .hex        (lastDataBits),
        .display    (HEX6)
    );

    seven_seg_hex seven_seg_inst_1
    (
        .clk        (clk_13p56_tmp),
        .rst_n      (rst_n),
        .en         (lastFrameSeenDataValid),
        .hex        (lastData[7:4]),
        .display    (HEX5)
    );

    seven_seg_hex seven_seg_inst_2
    (
        .clk        (clk_13p56_tmp),
        .rst_n      (rst_n),
        .en         (lastFrameSeenDataValid),
        .hex        (lastData[3:0]),
        .display    (HEX4)
    );

endmodule
