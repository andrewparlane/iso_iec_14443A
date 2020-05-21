/***********************************************************************
        File: driver.sv
 Description: The top level driver class (virtual)
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

package driver_pkg;

    virtual class Driver
    #(
        // IfaceType must include a clk signal for use in wait_for_idle
        type IfaceType,
        type TransType
    );

        // The start and run_thread tasks take a reference to a queue of TransType
        typedef TransType TransQueueType [$];

        // Our virtual iface
        IfaceType vif;

        // are we busy or idle?
        logic idle;

        // constructor
        function new (IfaceType _vif);
            vif = _vif;
            idle = 1'b1;
        endfunction

        // Call this to start the run thread
        virtual task start (ref TransQueueType q);
            fork
                begin
                    run_thread(q);
                end
            join_none
        endtask

        // The run_thread, this should never exit
        virtual protected task run_thread (ref TransQueueType q);
            idle = 1'b1;
            forever begin
                if (q.size() == 0) begin
                    idle = 1'b1;
                    wait (q.size() != 0) begin end
                end
                if (q.size()) begin
                    automatic TransType trans = q.pop_front;
                    idle = 1'b0;
                    process(trans);
                end
            end
        endtask

        // This should be overriden. It should place the transaction on the virtual iface
        pure virtual protected task process(TransType trans);

        virtual task wait_for_idle(int timeout=-1);
            // if we call this immediately after pushing something to the queue
            // then there's a race condition to see if this is run first or the run_thread
            // so just wait a little bit to give the run_thread a chance to start processing
            repeat (2) @(posedge vif.clk) begin end

            //$display("wait_for_idle(%d) called at %t", $time, timeout, $time);

            // we surround the main fork - join_any disable fork; with another fork
            // this is so that the disable fork; only disables this fork, and not
            // any parent forks (such as the one in start())
            // see: https://stackoverflow.com/a/14481391
            fork
                begin
                    fork
                        // process 1 - wait for idle
                        begin
                            //$display("process 1 - wait for idle");
                            wait (idle) begin end
                            //$display("process 1 - wait for idle - done at %t", $time);
                        end

                        // process 2 - timeout
                        begin
                            //$display("process 2 - timeout");
                            if (timeout > 0) begin
                                repeat (timeout) @(posedge vif.clk) begin end
                            end
                            else begin
                                forever @(posedge vif.clk) begin end
                            end
                            //$display("process 2 - timeout - done at %t", $time);
                            $error("wait_for_idle timed out after %d ticks", timeout);
                        end
                    join_any

                    disable fork;   // disable the other process
                end
            join
        endtask

    endclass

endpackage