/***********************************************************************
        File: analogue_sim.sv
 Description: Collects a bunch of components together for use with
              simulating the input to the ISO/IEC 14443A IP core
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

module analogue_sim
#(
    // The half period is rounded to the nearest ps
    // so the resulting clock not perfectly 13.56MHz
    parameter CLOCK_FREQ_HZ = 13560000  // 13.56MHz
)
(
    input           rst_n,
    output logic    picc_clk,               // this clock halts during Rx
    output logic    pcd_pause_n,            // the PCD's pause_n signal as received at the input to the analogue block
    output logic    pause_n_async,          // the delayed (non synchronised version of pcd_pause_n)
    output logic    pause_n_synchronised    // the latched and synchronised version of pause_n
);

    // generate the PCD clock
    logic pcd_clk;
    clock_source
    #(
        .CLOCK_FREQ_HZ  (CLOCK_FREQ_HZ)
    )
    clock_source_inst
    (
        .clk    (pcd_clk)
    );

    // our pcd_pause_n_iface which is passed to the driver, uses the pcd_clk
    // we only use an interface here because it has to be passed to the driver as a
    // virtual interface
    pcd_pause_n_iface iface (.clk(pcd_clk));
    assign pcd_pause_n = iface.pcd_pause_n;

    // the driver, this drives the iface.pcd_pause_n signal using the pcd_clk
    pcd_pause_n_driver_pkg::PCDPauseNDriver driver;

    // recover the PICC's clock from the "carrier wave"
    clk_recovery clk_recovery_inst
    (
        .pcd_clk        (pcd_clk),
        .pcd_pause_n    (iface.pcd_pause_n),
        .picc_clk       (picc_clk)
    );

    // detect the pause
    pause_detect pause_detect_inst
    (
        .pcd_pause_n    (iface.pcd_pause_n),
        .pause_n_async  (pause_n_async)
    );

    // latch and synchronise the pause_n_async signal
    // see the top level RTL module iso14443a_top.sv for an explanation
    pause_n_latch_and_synchroniser pause_n_latch_sync
    (
        .clk                    (picc_clk),
        .rst_n                  (rst_n),
        .pause_n_async          (pause_n_async),
        .pause_n_synchronised   (pause_n_synchronised)
    );

    function void init (int ticks_after_transaction             = 256,
                        int bit_ticks                           = 128,
                        int pause_ticks                         = 32,
                        int sequence_x_pause_start_offset_ticks = 64,
                        int sequence_z_pause_start_offset_ticks = 0);

        driver = new (iface, bit_ticks, pause_ticks,
                      sequence_x_pause_start_offset_ticks,
                      sequence_z_pause_start_offset_ticks,
                      ticks_after_transaction);
    endfunction

    task start (ref pcd_pause_n_transaction_pkg::PCDPauseNTransaction q [$]);
        // starts a new thread
        driver.start(q);
    endtask

    // Only call this when the driver is not transmitting
    function void set_bit_ticks (int _bit_ticks);
        driver.set_bit_ticks(_bit_ticks);
    endfunction

    // Only call this when the driver is not transmitting
    function void set_pause_ticks (int _pause_ticks);
        driver.set_pause_ticks(_pause_ticks);
    endfunction

    function void set_params(logic clock_stops,
                             int clock_stops_after_ps,
                             int clock_starts_after_ps,
                             int pause_n_asserts_after_ps,
                             int pause_n_deasserts_after_ps);
        clk_recovery_inst.set_params(clock_stops, clock_stops_after_ps, clock_starts_after_ps);
        pause_detect_inst.set_delays(pause_n_asserts_after_ps,  pause_n_deasserts_after_ps);
    endfunction

endmodule
