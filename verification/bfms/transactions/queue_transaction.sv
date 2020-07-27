/***********************************************************************
        File: queue_transaction.sv
 Description: Transactions base class for all transactions based on queues
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

package queue_transaction_pkg;

    import transaction_pkg::*;

    virtual class QueueTransaction
    #(
        type ElemType   // not the queue type, but the elements of the queue
    )
    extends Transaction;

        typedef ElemType QueueType [$];

        QueueType data;

        function new (QueueType _data = '{});
            data = _data;
        endfunction

        virtual function void fill_with_random(int len);
            data = '{};
            repeat (len) begin
                push_back($urandom);
            end
        endfunction

        virtual function void push_front(ElemType elem);
            data.push_front(elem);
        endfunction

        virtual function void push_back(ElemType elem);
            data.push_back(elem);
        endfunction

        virtual function void push_front_queue(QueueType _data);
            data = {_data, data};
        endfunction

        virtual function void push_back_queue(QueueType _data);
            data = {data, _data};
        endfunction

        virtual function ElemType pop_front;
            return data.pop_front;
        endfunction

        virtual function ElemType pop_back;
            return data.pop_back;
        endfunction

        virtual function int size;
            return data.size();
        endfunction

        virtual function logic compare (Transaction rhs);
            automatic QueueTransaction #(.ElemType(ElemType)) _rhs;
            if (!$cast(_rhs, rhs)) begin
                $fatal(0, "$cast failed");
            end
            return (data == _rhs.data);
        endfunction

        virtual function string to_string;
            return $sformatf("data: %p", data);
        endfunction
    endclass

    class ByteQueueTransaction
    extends QueueTransaction
    #(
        .ElemType (logic [7:0])
    );
        typedef logic BitQueue [$];

        function new (QueueType _data = '{});
            super.new(_data);
        endfunction

        static function ByteQueueTransaction new_random_transaction (int num_bytes);
            automatic ByteQueueTransaction res = new();
            res.fill_with_random(num_bytes);
            return res;
        endfunction

        function logic [15:0] calculate_crc;
            automatic logic [15:0] crc = 16'h6363;

            foreach (data[i]) begin
                // convert to 16 bit
                logic [15:0] ch;
                ch = {8'd0, data[i]};

                ch = ch ^ (crc & 16'h00FF);
                ch = (ch ^ ({ch[11:0], 4'd0} & 16'h00FF));

                crc = {8'd0, crc[15:8]} ^ {ch[7:0], 8'd0} ^ {ch[12:0], 3'd0} ^ {4'd0, ch[15:4]};
            end

            return crc;
        endfunction

        virtual function void append_crc;
            automatic logic [15:0] crc = calculate_crc;

            // add it to the data to send in little endien byte order
            push_back(crc[7:0]);
            push_back(crc[15:8]);
        endfunction

        // can be used with BitQueueTransaction::new()
        function BitQueue convert_to_bit_queue;
            // build a bit queue
            automatic BitQueue  bits = '{};
            automatic int       last_byte;

            foreach (data[i]) begin
                for (int b = 0; b < 8; b++) begin
                    bits.push_back(data[i][b]);
                end
            end

            return bits;
        endfunction
    endclass

    class BitQueueTransaction
    extends QueueTransaction
    #(
        .ElemType (logic)
    );

        function new (QueueType _data = '{});
            super.new(_data);
        endfunction

        static function BitQueueTransaction new_random_transaction (int num_bits);
            automatic BitQueueTransaction res = new();
            res.fill_with_random(num_bits);
            return res;
        endfunction

        virtual function void add_parity(int bits_in_first_byte=8);
            // create a new bit queue with the parity bits in
            automatic logic new_bits [$]    = '{};
            automatic int bit_count         = 0;
            automatic logic parity          = 1'b1;
            automatic int parity_after_bits = bits_in_first_byte;

            if (parity_after_bits == 0) begin
                parity_after_bits = 8;
            end

            // see ISO/IEC 14443-3:2016 section 6.2.3.2.1
            // parity is set so that the number of 1s is odd in each byte

            foreach (data[i]) begin
                new_bits.push_back(data[i]);

                if (data[i] == 1) begin
                    parity = !parity;
                end

                bit_count++;
                if (bit_count == parity_after_bits) begin
                    bit_count = 0;
                    new_bits.push_back(parity);
                    parity              = 1'b1;
                    parity_after_bits   = 8;
                end
            end

            // overwrite the data with the new one
            data = new_bits;
        endfunction

    endclass

endpackage
