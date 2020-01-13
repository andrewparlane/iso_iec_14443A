# ----------------------------------------------------------------------------------
# Requirements:
#	QuestaSim - We use vlog and vsim.
#	Each test bench must contain an instantiation called dut.
#	Each test bench must call $stop when it's finished testing.
# ----------------------------------------------------------------------------------

ifndef WLF
# set the default target to be all. Otherwise it's the first target it finds
.DEFAULT_GOAL := all
else
.DEFAULT_GOAL := view
endif

# Directories
SIM_DIR			= sim
WAVES_DIR		= $(SIM_DIR)/waves
SRC_DIR			= ../../iso14443a/hdl
PKG_DIR			= $(SRC_DIR)/pkg
TB_SRC_DIR		= ../tb

# src files
SRCS	= $(wildcard $(PKG_DIR)/*.sv) \
		  $(wildcard $(SRC_DIR)/*.sv)

# tb files
TB_SRCS	= $(wildcard $(TB_SRC_DIR)/*.sv)

# Extra arguments beyond the defaults in helper.mk
VCOM_FLAGS		=
VSIM_FLAGS		=

# Now include our helper.mk which has all the rules we need
# to create our library, compile and simulate our test benches
include helper.mk

# default rule is to create the library, and compile all the components
all: srcs tb_srcs

.PHONY: all

sequence_decode: all
	@$(call VSIM_CMD, sequence_decode_tb)

.PHONY: sequence_decode

# delete the library and all compiled files
clean: helper_clean

distclean: clean

.PHONY: clean distclean
