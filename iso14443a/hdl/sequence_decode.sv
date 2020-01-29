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
#(
    // We need to use different timings in the emulator project
    parameter bit EMULATOR_PROJECT = 0
)
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

    // outputs
    output ISO14443A_pkg::PCDBitSequence    seq,
    output logic                            seq_valid,
    output logic                            idle
);

    import ISO14443A_pkg::*;

    // ------------------------------------------------------------------------
    // Comments about how this code works
    // and how we calculate the timing values
    // ------------------------------------------------------------------------

    // when we have not seen a pause in more than two bit times, we go idle.
    // and then the first pause frame after being idle is assumed to be at the
    // start of the bit time. AKA sequence Z for start of comms.

    // We have a timer that counts the time between the rising edge of pause frames.
    // From that we can determine the current sequence. Since the clock stops during
    // pause frames, things are a bit more complicated.
    // Pause frames have according to ISO 14443-2A:2016 Table 4, have length between
    // 6 and 41 clock ticks, but the analogue front end (AFE) will change these timings a bit.
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
    //      X           pause       23              58          |   ERROR   (note: this is Z -> Z, but that's not valid)
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
    //       another Y and go idle. This is because the frame_decode module needs
    //       to also go idle

    // Note: When using the TRF7970A as the AFE in the emulation project. The pause lengths
    //       are more in the order of 100 ticks. Way out of range. To decode this data I had
    //       to change the timings to those listed below.

    //      previous    event       counter min     counter max |   result
    // ---------------------------------------------------------------------
    //      IDLE        pause       N/A             N/A         |   Z (SOC)
    //
    //      X           pause       0               16          |   ERROR
    //      X           pause       16              96          |   X
    //      X           timeout     97                          |   Y
    //
    //      Z           pause       0               15          |   ERROR
    //      Z           pause       16              95          |   Z
    //      Z           pause       96              160         |   X
    //      Z           timeout     161                         |   Y
    //
    //      Y           pause       0               63          |   z
    //      Y           pause       64              131         |   x
    //      Y           timeout     132                         |   IDLE

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
            last_pause_n    <= 1; // not in pause frame
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

    // have we timed out yet?
    logic timed_out;

    // we use different timings for the emulator project, due to the TRF7970A producing
    // crazy pause lengths in card emulation mode + DM0
    generate

        // ------------------------------------------------------------------------
        // ASIC design case
        // ------------------------------------------------------------------------

        if (!EMULATOR_PROJECT) begin

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

        end // !EMULATOR_PROJECT

        // ------------------------------------------------------------------------
        // EMULATOR PROJECT case
        // ------------------------------------------------------------------------

        else /* if (EMULATOR_PROJECT) */ begin

            always_comb begin
                // the next sequence depends on how long it's been since the last pause
                // and what the last sequence was
                case (seq)
                    PCDBitSequence_X: begin
                        // last sequence was an x
                        casez (counter)
                            9'b00000????:   seq_on_pause = PCDBitSequence_ERROR;    // if (counter < 9'd16)
                            default:        seq_on_pause = PCDBitSequence_X;        // else
                        endcase
                    end

                    PCDBitSequence_Z: begin
                        // last sequence was a Z
                        casez (counter)
                            9'b00000????:   seq_on_pause = PCDBitSequence_ERROR;    // if (counter < 9'd16)
                            9'b00001????:   seq_on_pause = PCDBitSequence_Z;
                            9'b0001?????:   seq_on_pause = PCDBitSequence_Z;
                            9'b0010?????:   seq_on_pause = PCDBitSequence_Z;        // else if (counter < 9'd96)
                            default:        seq_on_pause = PCDBitSequence_X;        // else
                        endcase
                    end

                    PCDBitSequence_Y: begin
                        casez (counter)
                            9'b000??????:   seq_on_pause = PCDBitSequence_Z;        // if (counter < 64)
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
                timed_out = ((seq == PCDBitSequence_X)     && (counter == 9'd97)) ||
                            ((seq == PCDBitSequence_Y)     && (counter == 9'd132)) ||
                            ((seq == PCDBitSequence_Z)     && (counter == 9'd161)) ||
                            ((seq == PCDBitSequence_ERROR) && (counter == 9'd384));
            end

        end // EMULATOR_PROJECT

    endgenerate

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            idle            <= 1;
            seq_valid       <= 0;
        end
        else begin
            // this should only be asserted for one tick at a time
            seq_valid <= 0;

            if (idle) begin
                // since we are idle then the first sequence we detect has to be Z
                // This is stated in ISO/IEC 14443-2:2016 section 8.1.3.1
                // start of communications is represented by a sequence Z
                if (pause_detected) begin
                    seq             <= PCDBitSequence_Z;
                    seq_valid       <= 1;
                    idle            <= 0;
                    counter         <= 1;   // reset the counter
                end
            end
            else begin
                // update the counter
                // default is to increment, but we override this later on if a pause
                // has been detected or a timeout has occured
                counter <= counter + 1'd1;

                if (pause_detected) begin
                    // when a pause is detected we reset the counter to 1
                    counter <= 1;

                    // and we issue a sequence, unless we previously errored
                    if (seq != PCDBitSequence_ERROR) begin
                        seq_valid <= 1;
                    end

                    seq <= seq_on_pause;
                end
                else begin
                    // no pause detected yet, have we timed out
                    if (timed_out) begin
                        // we have timed out and so this must be a Y
                        seq         <= PCDBitSequence_Y;
                        seq_valid   <= 1;
                        counter     <= 1;

                        if (seq == PCDBitSequence_Y) begin
                            // That's two Ys in a row, so we go idle now
                            idle <= 1;
                        end
                    end
                end
            end
        end
    end

endmodule
