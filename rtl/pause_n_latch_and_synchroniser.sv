/***********************************************************************
        File: pause_n_latch_and_synchroniser.sv
 Description: Latches and synchronises the pause_n asynchronous input
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

// Since the clock stops during pauses, it's possible there will never be a rising clock edge
// where pause_n_async is asserted. To solve this we could use a latch, with the pause_n_async
// connected to the asynchronous reset pin. When the pause has been received the latch is
// enabled passing a constant '1' through.

// The next issue is that the pause_n_async input is asynchronous, so connecting that to the async
// reset will mean the output of the latch is also asynchronous. Also if the pause deasserts
// while the ack_n signal is asserted, the output of the latch will deassert immediately meaning
// that may also happen asynchronously.
// Therefore we need a standard synchroniser on the output of the latch to prevent metastablity.

// Finally since the output of the synchroniser will only change on clock edges, we can use that
// as our ack_n signal. This will guarantee that the resulting latched and synchronised pause
// will be asserted for at least 1 tick.

// I tried this approach first, but if there are 0 rising clock edges between the pause_n_async
// asserting and deasserting, it takes 2 rising edges to get the pause_n_synchronised to assert
// which feeds back to the latch, and takes another 2 rising edges for pause_n_synchronised to
// deassert again. Which means it can take up to 4 clock periods after the pause_n_async deasserts
// before pause_n_synchronised deasserts. Whereas on the other extreme where there are at least 2
// clock edges before pause_n_async deasserts, pause_n_synchronised will have already asserted
// and so it only takes 2 more rising edges for it to deassert again, meaning the minimum time
// for pause_n_synchronised to deassert after pause_n_async deasserts is 1 clock period.
// The difference between that min and max is 3 clock periods or 221ns, which is more than half
// the margin we have for the FDT trigger. We can reduce this range by requiring the AFE to
// have at least 2 clock ticks before the pause_n_async deasserts, but that could be difficult to
// implement without adding extra delays to pause_n_async which kind of defeats the point.

// Instead I decided to use a FFD to latch the pause_n. The pause_n_async signal is connected
// to the active low reset pin, so the output immediately asserts when pause_n_async asserts.
// We then connect '1' to the D pin and our clock to the clock pin. So once pause_n_async has
// deasserted, on the next rising edge the output will deasssert.

// As before using the asynchronous reset on the FFD means the pause assertion is also asynchronous
// so we need the synchroniser. However since there's no feed back from the output of the synchroniser
// there always needs to be 3 rising edges for the pause_n_synchronised to deassert, giving a min time
// of 2 clock periods and a max time of 3 clock periods. The resulting range is then only 73.75ns,
// and the only requirement on the AFE is that the clock must start running before the pause_n_async
// deasserts. Which is the case with Fabricio's design.

// We connect the rst_n signal to the active low set pins on all the FFDs, so our reset
// clears any pauses.

module pause_n_latch_and_synchroniser
(
    input           clk,
    input           rst_n,
    input           pause_n_async,
    output logic    pause_n_synchronised
);

    logic pause_n_latched;

    // The "latching" flip flop
    // The D-Cells HD data book states that the reset pin takes priority
    // AKA if both reset and set are asserted, the output will be low.
    // So the tools have to modify this a little, inverting the logic and adding an inverter
    // to the output.
    always_ff @(posedge clk, negedge pause_n_async, negedge rst_n) begin
        if (!rst_n) begin               // active low SET pin
            pause_n_latched <= 1'b1;
        end
        else if (!pause_n_async) begin  // active low RESET pin
            pause_n_latched <= 1'b0;
        end
        else begin                      // rising edge of the clock
            pause_n_latched <= 1'b1;
        end
    end

    synchroniser
    #(
        .WIDTH      (1),    // 1 bit wide
        .RESET_VAL  (1'b1)  // resets to '1'
    )
    sync_inst
    (
        .clk        (clk),
        .rst_n      (rst_n),
        .d          (pause_n_latched),
        .q          (pause_n_synchronised)
    );

endmodule
