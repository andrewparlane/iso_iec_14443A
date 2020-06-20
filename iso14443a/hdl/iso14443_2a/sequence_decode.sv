/***********************************************************************
        File: sequence_decode.sv
 Description: Decode PCD -> PICC comms to sequences
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

module sequence_decode
(
    // clk is our 13.56MHz input clock. It is recovered from the carrier wave,
    // and as such stops during pause frames. It must not have any glitches.
    input                                   clk,

    // rst is our active low synchronised asynchronous reset signal
    input                                   rst_n,

    // pause_n_synchronised is the synchronised pause_n signal.
    // since the clock stops during pause frames, we can only expect pause_n_synchronised
    // to be asserted (0) for a couple of clock ticks.
    // So we just look for rising edges (end of pause)
    input                                   pause_n_synchronised,

    // outputs (BY_BYTE must be 0)
    rx_interface.out_bit                    out_iface
);

    import ISO14443A_pkg::*;

    // ------------------------------------------------------------------------
    // Comments about how this code works
    // and how we calculate the timing values
    // ------------------------------------------------------------------------

    // When we are idle, we assume the first pause we see is a PCDBitSequence_Z
    // which is the start of comms (SOC) define in ISO/IEC 14443-2:2016 section 8.1.3.1.
    // The end of comms (EOC) is defined in that same section as a logic '0' followed by a
    // PCDBitSequence_Y. When we have not seen a pause in more than two bit times, we go idle.
    // Any sequences received after EOC and before going idle are ignored. This is technically
    // an error but we are unlikely to have produced valid data if this happens and so we can
    // safely ignore them.

    // We have a timer that counts the time between the rising edge of pause frames,
    // from that we can determine the current sequence. Since the clock stops during
    // pause frames, things are a bit more complicated.
    // Pause frames according to ISO 14443-2A:2016 Table 4, have length between 6 and 41 clock
    // ticks, but the analogue front end (AFE) will change these timings a bit.
    // Adittionally to get a 6 tick pause, the reader would have to be doing something pretty
    // horrendous.

    // A bit time is 128 ticks.
    // Sequence X is a pause frame starting 64 ticks into the bit time.
    // Sequence Y is a bit time without any pause frames.
    // Sequence Z is a pause frame starting 0 ticks into the bit time.

    // See notes/rx_timings.* for info on how the below values are calculated

    // Cases:
    //      previous    event       counter min     counter max |   result
    // ---------------------------------------------------------------------
    //      IDLE        pause       N/A             N/A         |   Z (SOC)
    //
    //      X           pause       23              58          |   ERROR   (note: this is X -> Z, but that's not valid)
    //      X           pause       87              122         |   X
    //      X           timeout     132                         |   Y
    //
    //      Z           pause       87              122         |   Z
    //      Z           pause       151             186         |   X
    //      Z           timeout     196                         |   Y
    //
    //      Y           pause       19              54          |   z
    //      Y           pause       83              118         |   x
    //      Y           timeout     128                         |   IDLE

    // To allow for a little flexibilitiy we widen these ranges a bit.
    // and to reduce area I try to reuse comparators by merging similar limits
    // and closing the gaps between the ranges

    //      previous    event       counter min     counter max |   result
    // ---------------------------------------------------------------------
    //      IDLE        pause       N/A             N/A         |   Z (SOC)
    //
    //      X           pause       0               63          |   ERROR
    //      X           pause       64              131         |   X
    //      X           timeout     132                         |   Y
    //
    //      Z           pause       0               63          |   ERROR
    //      Z           pause       64              131         |   Z
    //      Z           pause       132             195         |   X
    //      Z           timeout     196                         |   Y
    //
    //      Y           pause       0               7           |   ERROR
    //      Y           pause       8               63          |   z
    //      Y           pause       64              131         |   x
    //      Y           timeout     132                         |   IDLE

    // Note: In the case of an ERROR we wait until we've had 3 bit periods of time
    //       without any pauses and then issue a Y, one bit time later we'll issue
    //       another Y and go idle. This allows us to issue the EOC

    // TODO: Should I support various timings here?
    //       The received pause length depends on the PCD and our analogue implementation.
    //       If we fabricate and get these timings wrong, then we will be unable to receive data.
    //       We could suupport 2 or 3 different sets of timings (short pulses, medium, long pulses)
    //       and then switch which mode to use using wire bonding?

    // ------------------------------------------------------------------------
    // End of pause detector
    // ------------------------------------------------------------------------

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
    // Decode the sequences
    // ------------------------------------------------------------------------

    // time between pauses, max value we care about is 384, so 9 bits
    logic [8:0] counter;

    // assuming a pause happens now, what would the next sequence be?
    PCDBitSequence seq_on_pause;

    // the current detected sequence
    PCDBitSequence seq;

    // is seq valid (asserts for only one tick at a time)
    logic seq_valid;

    // have we timed out yet?
    logic timed_out;

    always_comb begin
        // the next sequence depends on how long it's been since the last pause
        // and what the last sequence was
        case (seq)
            PCDBitSequence_X: begin
                // last sequence was an x
                casez (counter)
                    9'b000??????:   seq_on_pause = PCDBitSequence_ERROR;    // if (counter < 9'd64)
                    default:        seq_on_pause = PCDBitSequence_X;        // else
                endcase
            end

            PCDBitSequence_Z: begin
                // last sequence was a Z
                casez (counter)
                    9'b000??????:   seq_on_pause = PCDBitSequence_ERROR;    // if (counter < 9'd64)
                    9'b001??????:   seq_on_pause = PCDBitSequence_Z;
                    9'b0100000??:   seq_on_pause = PCDBitSequence_Z;        // else if (counter < 9'd132)
                    default:        seq_on_pause = PCDBitSequence_X;        // else
                endcase
            end

            PCDBitSequence_Y: begin
                casez (counter)
                    9'b000000???:   seq_on_pause = PCDBitSequence_ERROR;    // if (counter < 9'd8)
                    9'b000001???:   seq_on_pause = PCDBitSequence_Z;
                    9'b00001????:   seq_on_pause = PCDBitSequence_Z;
                    9'b0001?????:   seq_on_pause = PCDBitSequence_Z;        // else if (counter < 9'd64)
                    default:        seq_on_pause = PCDBitSequence_X;        // else
                endcase
            end

            // if the previous sequence wasn't a X, Y or Z, it must have bene an error
            // so the next sequence will be an error too
            default: seq_on_pause =  PCDBitSequence_ERROR;
        endcase
    end

    // have we timed out?
    always_comb begin
        timed_out = ((seq == PCDBitSequence_X)     && (counter == 9'd132)) ||
                    ((seq == PCDBitSequence_Y)     && (counter == 9'd132)) ||
                    ((seq == PCDBitSequence_Z)     && (counter == 9'd196)) ||
                    ((seq == PCDBitSequence_ERROR) && (counter == 9'd384));
    end

    logic detected_soc;     // have we seen the SOC
    logic idle;             // are we currently receiving sequences?

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            idle            <= 1'b1;
            seq_valid       <= 1'b0;
            detected_soc    <= 1'b0;
        end
        else begin
            // these should only be asserted for one tick at a time
            seq_valid       <= 1'b0;
            detected_soc    <= 1'b0;

            if (idle) begin
                // since we are idle then the first sequence we detect has to be Z
                // This is stated in ISO/IEC 14443-2:2016 section 8.1.3.1
                // start of communications is represented by a sequence Z
                if (pause_detected) begin
                    seq             <= PCDBitSequence_Z;
                    seq_valid       <= 1'b1;
                    detected_soc    <= 1'b1;
                    idle            <= 1'b0;
                    counter         <= 9'd1;   // reset the counter
                end
            end
            else begin
                // update the counter
                // default is to increment, but we override this later on if a pause
                // has been detected or a timeout has occured
                counter <= counter + 1'd1;

                if (pause_detected) begin
                    // when a pause is detected we reset the counter to 1
                    counter <= 9'd1;

                    // and we issue a sequence, unless we previously errored
                    if (seq != PCDBitSequence_ERROR) begin
                        seq_valid <= 1'b1;
                    end

                    seq <= seq_on_pause;
                end
                else begin
                    // no pause detected yet, have we timed out
                    if (timed_out) begin
                        // we have timed out and so this must be a Y
                        seq         <= PCDBitSequence_Y;
                        seq_valid   <= 1'b1;
                        counter     <= 9'd1;

                        if (seq == PCDBitSequence_Y) begin
                            // That's two Ys in a row, so we go idle now
                            idle <= 1'b1;
                        end
                    end
                end
            end
        end
    end

    // ------------------------------------------------------------------------
    // Turn the sequences into bits/SOC/EOC/error
    // ------------------------------------------------------------------------

    // cache the last sequence, so we can detect EOC
    PCDBitSequence  prev;
    logic           prev_is_soc;
    logic           in_frame;

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            out_iface.soc           <= 1'b0;
            out_iface.eoc           <= 1'b0;
            out_iface.error         <= 1'b0;
            out_iface.data_valid    <= 1'b0;
            in_frame                <= 1'b0;
        end
        else begin
            // these should only assert for one tick
            out_iface.soc           <= 1'b0;
            out_iface.eoc           <= 1'b0;
            out_iface.error         <= 1'b0;
            out_iface.data_valid    <= 1'b0;

            // only do something if we have a valid seq
            if (seq_valid) begin
                // cache the current seq
                prev        <= seq;
                prev_is_soc <= detected_soc;

                if (detected_soc) begin
                    // do nothing, as we use prev for all tests
                    // so must wait for the next sequence
                end
                else begin
                    if (prev_is_soc) begin
                        // Issue our SOC and start the frame
                        out_iface.soc           <= 1'b1;
                        in_frame                <= 1'b1;
                    end
                    else if (in_frame) begin
                        // we emit nothing when we aren't in a frame
                        if (((prev == PCDBitSequence_Y) || (prev == PCDBitSequence_Z)) &&
                            (seq == PCDBitSequence_Y)) begin
                            // it's the EOC if we have logic '0' followed by Y
                            // See ISO/IEC 14443-2:2016 section 8.1.3.1
                            // Issue the EOC and end the frame
                            out_iface.eoc           <= 1'b1;
                            in_frame                <= 1'b0;
                        end
                        else if (prev == PCDBitSequence_ERROR) begin
                            // there was a timing error
                            // seq_valid doesn't go high again until we've timed out
                            // so this can only happens once
                            out_iface.error         <= 1'b1;
                        end
                        else begin
                            // we're not SOC, EOC or an error, and we're in a frame
                            // emit the data bit
                            out_iface.data_valid    <= 1'b1;
                            // PCDBitSequence_X -> 1, PCDBitSequence_Y -> 0, PCDBitSequence_Z -> 0
                            out_iface.data          <= (prev == PCDBitSequence_X);
                        end
                    end
                end
            end
        end
    end

endmodule
