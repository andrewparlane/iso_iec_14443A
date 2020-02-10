/***********************************************************************
        File: fdt.sv
 Description: Triggers the Tx module to start sending at the correct time
      Author: Andrew Parlane
************************************************************************/

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

// ISO/IEC 14443-3:2016 section 6.2.1.1 defines the frame delay time between PCD messages
// and PICC replies.
// The frame delay time is the time between the rising edge of the last pause from the PCD
// and the first modulation edge of the reply.
// The FDT time changes based on if the last bit of the PCD's message was a 1 or a 0
// since that changes where the last pause is.

// For initialisation / AC messages, there is only one option for the FDT trigger.
// For other messages the FDT trigger can occur a number of whole bit times after the initial
// timeout. We don't support this. You must be ready to send by the first trigger.

// Since the pause_n_synchronised signal passes through two FFDs to be synchronised
// and the first modulation edge happens a few ticks after the trigger, we have to
// take that into account. Additionally there is potential delays in the AFE.

// The measured FDT time must be within the specified value and the specified value + 0.4µs
// 0.4µs = 5.424 ticks.

module fdt
#(
    // Timing adjust should consist of two parts:
    //      parameter real PCD_PAUSE_N_TO_SYNCHRONISED_PS,
    //      parameter real TRIGGER_TO_MODULATION_EDGE_PS
    // specifically:
    //      parameter int TIMING_ADJUST = $rtoi((PCD_PAUSE_N_TO_SYNCHRONISED_PS +
    //                                           TRIGGER_TO_MODULATION_EDGE_PS) / CLOCK_PERIOD_PS);

    // PCD_PAUSE_N_TO_SYNCHRONISED_PS: This should be the time in ps between the start of
    // the rising edge of the analogue RF signal (see small circles in Figure 3 of
    // ISO/IEC 14443-2:2016, I think the one labled as 5, but the docs aren't clear),
    // and the rising edge of the pause_n_synchronised signal.
    // There are three parts to this:
    //      How long does it take from the analogue RF signal returning before the
    //          digital signal (pause_n) deasserts.
    //      When does the clock generator start providing a clock again?
    //      How longe does it take for the synchroniser to deassert pause_n_synchronised.

    // TRIGGER_TO_MODULATION_EDGE_PS: This should be the time in ps between the rising edge
    // of the trigger output (of this module) and the load modulation activing.
    // This is probably dominated by the Tx module, (one tick to see the trigger, and one tick
    // to see the enable signal and assert the output data. But there will be a slight delay
    // due to the output buffering and in the AFE before the load modulation circuit activates

    // Note: We can NOT trigger early, but we have a fair bit of leeway to trigger late.
    //       so choose the minimum times for the above values. For this same reason we use
    //       the $rtoi() function to set TIMING_ADJUST. Since this truncates the real value
    //       rather than rounding to the nearest value.
    //       Remember that the our clock can be 180 degrees out of phase with the PCD's clock
    //       depending on how long the pauses are and when the clock generator stops / starts
    //       producing the clock. So we should check both options and pick the smallest.

    // TODO: We should run gate level simulations of the AFE + synchroniser.
    // TODO: We should run gate level simulations of the output buffer + AFE

    parameter int TIMING_ADJUST
)
(
    // clk is our 13.56MHz input clock.
    input               clk,

    // rst_n is our active low synchronised asynchronous reset signal
    input               rst_n,

    // pause_n_synchronised is the synchronised pause_n signal.
    // since the clock stops during pause frames, we can only expect pause_n_synchronised
    // to be asserted (0) for a couple of clock ticks.
    // So we just look for rising edges (end of pause)
    input               pause_n_synchronised,

    input               last_rx_bit,

    // trigger Tx
    output logic        trigger
);
    // ------------------------------------------------------------------------
    // parameters
    // ------------------------------------------------------------------------

    // largest value is 1236 = 11 bits
    localparam logic [10:0] FDT_LAST_BIT_0 = 11'(1172 - TIMING_ADJUST);
    localparam logic [10:0] FDT_LAST_BIT_1 = 11'(1236 - TIMING_ADJUST);

    // ------------------------------------------------------------------------
    // End of pause detector
    // ------------------------------------------------------------------------
    // copied from sequence_decode.sv

    logic last_pause_n;   // previous value of pause_n_synchronised
    logic pause_detected; // have we detected a pause? (risring edge of pause_n_synchronised)

    assign pause_detected = (last_pause_n == 0) && (pause_n_synchronised == 1);

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            last_pause_n    <= 1'b1; // not in pause frame
        end
        else begin
            // update cached value
            last_pause_n <= pause_n_synchronised;
        end
    end

    // ------------------------------------------------------------------------
    // timer
    // ------------------------------------------------------------------------

    logic [10:0] count;
    logic seen_pause;

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            trigger     <= 1'b0;
            count       <= '0;
            seen_pause  <= 1'b0;
        end
        else begin
            // trigger should only assert for one tick at a time
            trigger     <= 1'b0;

            if (pause_detected) begin
                seen_pause  <= 1'b1;

                // it took us one tick to see the pause_detected signal
                // and on the next tick when we check the counter it will have
                // been 2 ticks
                count       <= 11'd2;
            end
            else if (seen_pause) begin
                // we've seen a pause since we last triggered so
                // check if we are ready to trigger
                // note: last_bit can't change much after the last pause
                //       so we don't have to worry about it changing between the two
                //       timeouts and causing issues.
                if ((!last_rx_bit && (count == FDT_LAST_BIT_0)) ||
                    (last_rx_bit && (count == FDT_LAST_BIT_1))) begin
                    // we have timed out
                    trigger     <= 1'b1;

                    // stop counting and wait for the next pause
                    seen_pause  <= 1'b0;
                end

                // update the counter
                count <= count + 1'd1;
            end
        end
    end

endmodule
