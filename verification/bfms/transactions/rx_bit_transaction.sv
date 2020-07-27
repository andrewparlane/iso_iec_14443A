/***********************************************************************
        File: rx_bit_transaction.sv
 Description: Transaction for the Rx bit interface
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

package rx_bit_transaction_pkg;

    import transaction_pkg::*;
    import queue_transaction_pkg::*;

    class RxBitTransaction
    extends queue_transaction_pkg::BitQueueTransaction;

        typedef ISO14443A_pkg::PCDBitSequence PCDBitSequenceQueue [$];

        function new (logic _data [$] = '{});
            super.new(_data);
        endfunction

        static function RxBitTransaction new_random_transaction (int num_bits);
            automatic RxBitTransaction res = new();
            res.fill_with_random(num_bits);
            return res;
        endfunction

        // can be used with PCDPauseNSequence::new()
        virtual function PCDBitSequenceQueue convert_to_pcd_sequence_queue;
            // build up a PCDBitSequence queue
            automatic PCDBitSequenceQueue seqs = '{};

            // See ISO/IEC 14443-2:2106 section 8.1.3.1

            // Start of comms
            seqs.push_back(ISO14443A_pkg::PCDBitSequence_Z);

            // data
            foreach (data[i]) begin
                if (data[i]) begin
                    // 1 -> X
                    seqs.push_back(ISO14443A_pkg::PCDBitSequence_X);
                end
                else begin
                    // 0 -> if previous sequence was a Y or a Z, then we send Z. Otherwise Y
                    if (seqs[$] == ISO14443A_pkg::PCDBitSequence_X) begin
                        seqs.push_back(ISO14443A_pkg::PCDBitSequence_Y);
                    end
                    else begin
                        seqs.push_back(ISO14443A_pkg::PCDBitSequence_Z);
                    end
                end
            end

            // end of comms: logic '0' followed by sequence Y
            if (seqs[$] == ISO14443A_pkg::PCDBitSequence_X) begin
                seqs.push_back(ISO14443A_pkg::PCDBitSequence_Y);
            end
            else begin
                seqs.push_back(ISO14443A_pkg::PCDBitSequence_Z);
            end

            seqs.push_back(ISO14443A_pkg::PCDBitSequence_Y);

            // note: sequence_decode requires two sequence Ys in a row to go idle
            //       whereas we could be finishing with YY or ZY.
            //       Therefore the driver should ensure there is at least two full bit time
            //       of idle between any two transactions

            return seqs;
        endfunction

    endclass

    class RxMonitorBitTransaction
    extends RxBitTransaction;

        logic error;

        function new (logic _data [$] = '{}, logic _error = 1'b0);
            super.new(_data);
            error = _error;
        endfunction

        static function RxMonitorBitTransaction new_random_transaction (int num_bits, int _error=-1);
            automatic RxMonitorBitTransaction res = new();
            res.fill_with_random(num_bits);
            res.error = (_error == -1) ? 1'($urandom) : 1'(_error);
            return res;
        endfunction

        virtual function logic compare (Transaction rhs);
            automatic RxMonitorBitTransaction _rhs;
            if (!$cast(_rhs, rhs)) begin
                $fatal(0, "$cast failed");
            end

            // if we got an error but weren't expecting one
            // or if we expected an error but didn't get one
            // then the transactions aren't equal
            if (error != _rhs.error) begin
                return 1'b0;
            end

            // if we detected an error then ignore the data and count the frames as equal
            if (error) begin
                return 1'b1;
            end

            // otherwise ...
            return super.compare(_rhs);
        endfunction

        virtual function string to_string;
            return {super.to_string, $sformatf(", error: %b", error)};
        endfunction
    endclass

endpackage
