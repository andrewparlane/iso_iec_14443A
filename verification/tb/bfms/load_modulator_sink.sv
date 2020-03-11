/***********************************************************************
        File: load_modulator_sink.sv
 Description: Sink for the tx_out signal of the tx module
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

module load_modulator_sink
(
    input   clk,
    input   rst_n,
    input   tx_out
);

    typedef logic dataQueue [$];

    dataQueue   received;

    function automatic void initialise;
        received.delete;
    endfunction

    function automatic void clear_received_queue;
        received.delete;
    endfunction

    function automatic dataQueue get_and_clear_received_queue;
        automatic dataQueue res = received;
        received.delete;
        return res;
    endfunction

    function automatic logic received_queue_is_empty;
        return received.size == 0;
    endfunction

    // ========================================================================
    // Receive and decode
    // ========================================================================
    // ISO/IEC 14443-2:2016 section 8.2.1
    //      one bit time is 128 ticks
    // ISO/IEC 14443-2:2016 section 8.2.5.1
    //      we are idle if it's all 0s
    //      a 1 is represented by 64 1s then 64 0s, ANDd with th esubcarrier
    //      a 0 is represented by 64 0s then 64 1s, ANDd with th esubcarrier
    // ISO/IEC 14443-2:2016 section 8.2.4
    //      The subcarrier has frequency of fc/16 and the bit period start with the subcarrier high

    localparam logic [127:0] IDLE = '0;
    localparam logic [127:0] TX_0 = {64'b0, {4{8'hFF, 8'h00}}};
    localparam logic [127:0] TX_1 = {{4{8'hFF, 8'h00}}, 64'b0};

    // pass the input through a 128 bit shift register, to capture an entire bit
    logic [127:0] tx_sr;
    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            tx_sr <= '0;
        end
        else begin
            tx_sr <= {tx_sr[126:0], tx_out};
        end
    end

    logic   idle;
    int     tick_count;
    always_ff @(posedge clk, negedge rst_n) begin: rxData
        if (!rst_n) begin
            idle <= 1'b1;
        end
        else begin: risingEdgeClk
            if (idle) begin: isIdle
                // wait for first rising edge (must be a 1 as that's SOC)
                if (tx_out) begin: leavingIdle
                    idle        <= 1'b0;
                    tick_count  <= 1;

                    rxQueueEmptyOnLeavingIdle: assert (received.size == 0)
                        else $error("Received queue contains entries when going none idle");
                end
            end
            else begin: notIdle
                if (tick_count == 128) begin: bitReceived
                    // full bit received parse it
                    validPattern:
                    assert ((tx_sr == IDLE) || (tx_sr == TX_0) || (tx_sr == TX_1))
                        else $error("Received %b is not a valid bit pattern", tx_sr);

                    if (tx_sr == IDLE) begin
                        // done, go idle
                        idle <= 1'b1;
                    end
                    else if (tx_sr == TX_0) begin
                        received.push_back(1'b0);
                    end
                    else if (tx_sr == TX_1) begin
                        received.push_back(1'b1);
                    end

                    // start receiving the next bit
                    tick_count <= 1;
                end
                else begin
                    tick_count <= tick_count + 1;
                end
            end
        end
    end

    // ========================================================================
    // Timeouts
    // ========================================================================

    task automatic wait_for_idle(int timeout=0);
        fork
            // process 1, timeout
            begin
                if (timeout == 0) begin
                    forever @(posedge clk) begin end
                end
                else begin
                    repeat (timeout) @(posedge clk) begin end
                end
                $error("wait_for_idle timed out after %d ticks", timeout);
            end

            // process 2 - wait for us to go idle
            begin
                wait (idle) begin end
            end

        // finish as soon as any of these processes finish
        join_any

        // disable the remaining process
        disable fork;
    endtask

    // ========================================================================
    // Asserts
    // ========================================================================

    // we error if the received data isn't idle, a 1 or a 0. Meaning we'd catch
    // any glitches or incorrect patterns.
    // So I don't think we need many asserts here

    // Check that the tx_out is low when we are in reset
    signalsInReset:
    assert property (
        @(posedge clk)
        !rst_n |-> !tx_out)
        else $error("tx_out asserted whilst in reset");

    // check tx_out is never unknown
    txOutNotUnknown:
    assert property (
        @(posedge clk)
        !$isunknown(tx_out))
        else $error("tx_out unknown");

endmodule
