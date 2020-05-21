/***********************************************************************
        File: monitor.sv
 Description: The top level monitor class (virtual)
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

package monitor_pkg;

    virtual class Monitor
    #(
        type IfaceType,
        type TransType
    );

        // The start and run_thread tasks take a reference to a queue of TransType
        typedef TransType TransQueueType [$];

        // Our virtual iface
        IfaceType vif;

        // are we busy or idle?
        logic idle;

        // events
        event packet_receieved;

        // constructor
        function new (IfaceType _vif);
            vif     = _vif;
            idle    = 1'b1;
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
            forever begin
                automatic TransType trans;
                automatic logic     res     = 1'b0;

                process(trans, res);
                if (res) begin
                    q.push_back(trans);
                    -> packet_receieved;    // trigger an event
                end
            end
        endtask

        // This should be overriden. It should detect a transaction from the virtual iface
        // and store it in trans. res should be set to 1'b1 to indicate success
        // It must also set the idle flag appropriately
        pure virtual protected task process(output TransType trans, output logic res);

        // because we never know if another transaction is about to start
        // we wait until we are idle for more than X ticks, it's up to the user
        // to determine what X should be (max ticks between transactions)
        virtual task wait_for_idle(int required_idle_ticks, int timeout=-1);
            //$display("wait_for_idle(%d, %d) called at %t", required_idle_ticks, timeout, $time);

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
                            forever begin
                                automatic int count;

                                wait (idle) begin end

                                // we are now idle, we need to be idle for the next required_idle_ticks ticks
                                for (count = required_idle_ticks; count > 0; count--) begin
                                    @(posedge vif.clk) begin end
                                    if (!idle) begin
                                        break;
                                    end
                                end

                                if (count == 0) begin
                                    // success
                                    break;
                                end

                                // otherwise wait for idle again
                            end
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

        virtual task wait_for_packet_received(int timeout=-1, logic error_on_timeout=1'b1);
            //$display("wait_for_packet_received(%d, %b) called at %t", timeout, error_on_timeout, $time);

            // we surround the main fork - join_any disable fork; with another fork
            // this is so that the disable fork; only disables this fork, and not
            // any parent forks (such as the one in start())
            // see: https://stackoverflow.com/a/14481391
            fork
                begin
                    fork
                        // process 1 - wait for packet received
                        begin
                            //$display("process 1 - wait for packet received");
                            wait (packet_receieved.triggered) begin end
                            //$display("process 1 - wait for packet received - done at %t", $time);
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
                            if (error_on_timeout) begin
                                $error("wait_for_packet_received timed out after %d ticks", timeout);
                            end
                        end
                    join_any

                    disable fork;   // disable the other process
                end
            join
        endtask

    endclass

endpackage