#***********************************************************************
#        File: emulation.sdc
# Description: Timing constraints for the emulation project
#      Author: Andrew Parlane
#***********************************************************************


# This file is part of https://github.com/andrewparlane/fiuba_thesis/blob/master/LICENSE
# Copyright (c) 2020 Andrew Parlane.
#
# This is free software: you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free
# Software Foundation, version 3.
#
# This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
# General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this code. If not, see <http://www.gnu.org/licenses/>.

# Add our 50MHz input clock
create_clock -name "clk50MHz" -period 20.000ns [get_ports {CLOCK_50}] -waveform {10.000 20.000}

# Auto get our PLL clocks
derive_pll_clocks -create_base_clocks

# Cut asynch paths
set_false_path -from [get_ports KEY[*]]
set_false_path -from [get_ports PAUSE]
set_false_path -to   [get_ports TX]
set_false_path -to   [get_ports LEDG[*]]
set_false_path -to   [get_ports LEDR[*]]
set_false_path -to   [get_ports HEX4[*]]
set_false_path -to   [get_ports HEX5[*]]
set_false_path -to   [get_ports HEX6[*]]
