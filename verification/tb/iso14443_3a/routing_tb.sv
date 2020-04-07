/***********************************************************************
        File: routing_tb.sv
 Description: Testbench for routing
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

module routing_tb;

    // --------------------------------------------------------------
    // Ports to DUT
    // all named the same as in the DUT, so I can use .*
    // --------------------------------------------------------------

    logic route_rx_to_initialisation;
    logic route_rx_to_14443_4;
    logic route_tx_from_14443_4;
    logic in_tx_append_crc_init;
    logic in_tx_append_crc_14443_4;
    logic out_tx_append_crc;

    // Rx interfaces
    rx_interface #(.BY_BYTE(1), .USE_ASSERTS(0)) in_rx_iface            (.*);
    rx_interface #(.BY_BYTE(1), .USE_ASSERTS(0)) out_rx_iface_init      (.*);
    rx_interface #(.BY_BYTE(1), .USE_ASSERTS(0)) out_rx_iface_14443_4   (.*);

    // Tx interfaces
    tx_interface #(.BY_BYTE(1), .USE_ASSERTS(0)) in_tx_iface_init       (.*);
    tx_interface #(.BY_BYTE(1), .USE_ASSERTS(0)) in_tx_iface_14443_4    (.*);
    tx_interface #(.BY_BYTE(1), .USE_ASSERTS(0)) out_tx_iface           (.*);

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------

    routing dut (.*);

    // --------------------------------------------------------------
    // Clock generator
    // --------------------------------------------------------------

    // Calculate our clock period in ps
    localparam CLOCK_FREQ_HZ = 13560000; // 13.56MHz
    localparam CLOCK_PERIOD_PS = 1000000000000.0 / CLOCK_FREQ_HZ;

    logic clk;
    logic rst_n;

    initial begin
        clk = 1'b0;
        forever begin
            #(int'(CLOCK_PERIOD_PS/2))
            clk = ~clk;
        end
    end

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin: testStimulus
        automatic logic [2:0] routings[$] = '{3'b010, 3'b101, 3'b110, 3'b111};
        automatic int i = 0;
        rst_n <= 1'b1;

        // test 4 cases:
        //  1) just to / from initialialisation
        //  2) just to / from 14443_4
        //  3) to both, from initialise
        //  4) to both, from 14443_4
        // note: For some reason using foreach (routings[i]) begin: routingsLoop
        //       gives an unnamed assertion warning and adds an extra "unamed$$_0"
        //       to the assertion paths.
        repeat (4) begin: routingLoop
            {route_rx_to_14443_4,
             route_rx_to_initialisation,
             route_tx_from_14443_4}         = routings[i++];

            // just randomize all the DUTs inputs (other than the control signals)
            repeat (10000) begin: repeatLoop
                in_rx_iface.soc                 = 1'($urandom);
                in_rx_iface.eoc                 = 1'($urandom);
                in_rx_iface.error               = 1'($urandom);
                in_rx_iface.data                = 8'($urandom);
                in_rx_iface.data_valid          = 1'($urandom);
                in_rx_iface.data_bits           = 3'($urandom);

                in_tx_iface_init.data           = 8'($urandom);
                in_tx_iface_init.data_valid     = 1'($urandom);
                in_tx_iface_init.data_bits      = 3'($urandom);

                in_tx_iface_14443_4.data        = 8'($urandom);
                in_tx_iface_14443_4.data_valid  = 1'($urandom);
                in_tx_iface_14443_4.data_bits   = 3'($urandom);

                out_tx_iface.req                = 1'($urandom);

                in_tx_append_crc_init           = 1'($urandom);
                in_tx_append_crc_14443_4        = 1'($urandom);

                #10 begin end
                rxSocInit:          assert (out_rx_iface_init.soc           == (route_rx_to_initialisation ? in_rx_iface.soc : 1'b0))           else $error("Rx SOC not routed correctly");
                rxSoc4:             assert (out_rx_iface_14443_4.soc        == (route_rx_to_14443_4        ? in_rx_iface.soc : 1'b0))           else $error("Rx SOC not routed correctly");

                rxEocInit:          assert (out_rx_iface_init.eoc           == (route_rx_to_initialisation ? in_rx_iface.eoc : 1'b0))           else $error("Rx EOC not routed correctly");
                rxEoc4:             assert (out_rx_iface_14443_4.eoc        == (route_rx_to_14443_4        ? in_rx_iface.eoc : 1'b0))           else $error("Rx EOC not routed correctly");

                rxErrorInit:        assert (out_rx_iface_init.error         == (route_rx_to_initialisation ? in_rx_iface.error : 1'b0))         else $error("Rx error not routed correctly");
                rxError4:           assert (out_rx_iface_14443_4.error      == (route_rx_to_14443_4        ? in_rx_iface.error : 1'b0))         else $error("Rx error not routed correctly");

                rxDataValidInit:    assert (out_rx_iface_init.data_valid    == (route_rx_to_initialisation ? in_rx_iface.data_valid : 1'b0))    else $error("Rx data_valid not routed correctly");
                rxDataValid4:       assert (out_rx_iface_14443_4.data_valid == (route_rx_to_14443_4        ? in_rx_iface.data_valid : 1'b0))    else $error("Rx data_valid not routed correctly");

                rxDataBitsInit:     assert (out_rx_iface_init.data_bits     == in_rx_iface.data_bits)                                           else $error("Rx data_bits not routed correctly");
                rxDataBits4:        assert (out_rx_iface_14443_4.data_bits  == in_rx_iface.data_bits)                                           else $error("Rx data_bits not routed correctly");

                rxDataInit:         assert (out_rx_iface_init.data          == in_rx_iface.data)                                                else $error("Rx data not routed correctly");
                rxData4:            assert (out_rx_iface_14443_4.data       == in_rx_iface.data)                                                else $error("Rx data not routed correctly");

                // Tx checks
                txData:         assert (out_tx_iface.data       == (route_tx_from_14443_4   ? in_tx_iface_14443_4.data          : in_tx_iface_init.data))       else $error("Tx data not routed correctly");
                txDataValid:    assert (out_tx_iface.data_valid == (route_tx_from_14443_4   ? in_tx_iface_14443_4.data_valid    : in_tx_iface_init.data_valid)) else $error("Tx data_valid not routed correctly");
                txDataBits:     assert (out_tx_iface.data_bits  == (route_tx_from_14443_4   ? in_tx_iface_14443_4.data_bits     : in_tx_iface_init.data_bits))  else $error("Tx data_bits not routed correctly");

                txReqInit:      assert (in_tx_iface_init.req    == (!route_tx_from_14443_4  ? out_tx_iface.req                  : 1'b0))                        else $error("Tx req not routed correctly");
                txReq4:         assert (in_tx_iface_14443_4.req == (route_tx_from_14443_4   ? out_tx_iface.req                  : 1'b0))                        else $error("Tx req not routed correctly");

                txAppendCRC:    assert (out_tx_append_crc       == (route_tx_from_14443_4   ? in_tx_append_crc_14443_4          : in_tx_append_crc_init))       else $error("Tx append_crc not routed correctly");

                #10 begin end
            end
        end

        $stop;
    end

endmodule
