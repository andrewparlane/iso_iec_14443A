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
    input           [0:0]   GPIO_0, // our pause_n input
    output logic    [8:0]   LEDG
);

    // ========================================================================
    // Aliases
    // ========================================================================

    // KEY[0] is active low rst
    logic rst_n;
    assign rst_n = KEY[0];

    // GPIO_0[0] is pause_n
    logic pause_n;
    assign pause_n = GPIO_0[0];

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
    logic pause_n_synchronised_13p56;

    // note: we use clk_13p56_tmp so that we don't get stuck when the clock is stopped
    always_ff @(posedge clk_13p56_tmp, negedge rst_n) begin
        if (!rst_n) begin
            pause_n_tmp                 <= 1;
            pause_n_synchronised_13p56  <= 1;
        end
        else begin
            pause_n_synchronised_13p56  <= pause_n_tmp;
            pause_n_tmp                 <= pause_n;
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
            // enable the clk when pause_n_synchronised_13p56 is high
            // disable it when it is low
            clk_13p56_en <= pause_n_synchronised_13p56;

            if (pause_n_synchronised_13p56 == 0) begin
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

    iso14443a_top dut
    (
        .clk        (clk_13p56),
        .rst_n      (iso14443_rst_n),

        .pause_n    (pause_n)
    );

    // ========================================================================
    // LEDs (active high)
    // ========================================================================

    assign LEDG[0]  = !rst_n;
    assign LEDG[1] = iso14443_rst_n;
    assign LEDG[2] = clk_13p56_tmp_locked;
    assign LEDG[3] = clk_13p56_en;
    assign LEDG[4] = pause_n;
    assign LEDG[5] = 0;
    assign LEDG[6] = 0;
    assign LEDG[7] = 0;
    assign LEDG[8] = 0;

endmodule
