/***********************************************************************
        File: pcd_pause_n_transaction.sv
 Description: Transactions for use with the pcd_pause_n driver
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

package pcd_pause_n_transaction_pkg;

    import transaction_pkg::*;

    class PCDPauseNTransaction
    extends queue_transaction_pkg::QueueTransaction
    #(
        .ElemType (ISO14443A_pkg::PCDBitSequence)
    );

        function new (ISO14443A_pkg::PCDBitSequence _data [$] = '{});
            super.new(_data);
        endfunction

        virtual function logic compare (Transaction rhs);
            automatic PCDPauseNTransaction _rhs;
            if (!$cast(_rhs, rhs)) begin
                $fatal(0, "$cast failed");
            end
            return (data == _rhs.data);
        endfunction

        virtual function string to_string;
            return $sformatf("data: %p", data);
        endfunction

    endclass

endpackage
