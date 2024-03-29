# ----------------------------------------------------------------------------------
#        File: Makefile
# Description: Makefile to build and run testbenches with VCS
#      Author: Andrew Parlane
# ----------------------------------------------------------------------------------

# This file is part of https://github.com/andrewparlane/iso_iec_14443a
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

# ----------------------------------------------------------------------------------
# Tested with Synopsys VCS on micro0.fi.uba.ar:
# 	vcs script version : O-2018.09
#	Compiler version = VCS-MX O-2018.09-SP2_Full64
#	VCS Build Date = Feb 28 2019 22:34:30
# ----------------------------------------------------------------------------------

# Prerequisites:
#   Set up your environment on the machine you have vcs installed on
#		This can be done using the /usr/synopsys2/synopsys_rc script (at least on micro0.fi.uba.ar)
#		You may need to copy it to your user directory and chmod 755 it in order to gain execute perms.
#		If you have errors with vcs along the lines of "/usr/bin/ld unrecognised option -plugin"
#		then comment out the HSPICE source line in that script.
#		You can add ". ~/synopsys_rc" to your .bashrc script if desired.
# 	set the REMOTE_SERVER and REMOTE_PATH vars below
#		If you want to edit the files on your local machine and run vcs on a server
#		then you can use the push_to_remote and connect_to_remote rules to make life easier.
#		REMOTE_SERVER is username@server.address
#		REMOTE_PATH is where you want to push the files either /absolute/path/to/dest
#		or ~/relative/path/from/home/dir.
#		If you wish to use the GUI (DVE / VERDI) on the remote server then you must have the ability
#		to launch X apps remotely via ssh -X, I'm not sure how this works with linux, but with
#		cygwin follow: https://codeyarns.com/2018/04/01/how-to-use-cygwin-x-server-for-local-and-remote/
# 	set all the directory vars correctly
#		ROOT_DIR should be a relative or absolute path to the top level repository dir
#		SRC_DIR is the relative path from ROOT_DIR to the source files.
#		PKG_DIR is the relative path from ROOT_DIR to a dir with packages in
#		TB_SRC_DIR is the relative path from ROOT_DIR to the testbenches
# 		VCS_DIR is the relative path from ROOT_DIR to the directory that contains this Makefile
#		SRCS should be a list of all sources files (including testbenches). Packages should come first
#		TBS should be a list of module names of testbenches. This is used to build the Makefile rules
#	edit the _ARGS vars as required
#		VLOGAN_ARGS
#		VCS_ARGS
#		SIMV_ARGS

# Rules (where X is one of the values in $(TBS)):
#	list_tbs:			prints a list of known testbenches
#	analyse: 			analyse all source files using vlogan
#	elaborate: 			elaborate all testbenches into _simv binaries
# 	X_simv:				elaborate the X into the X_simv binary
#	X:					run the X simulation (executes ./X_simv)
#	clean:				deletes all generated files
#	push_to_remote:		syncs local files to the remote server
# 	connect_to_remote:	ssh to the remote server and cd to the vcs dir

# Macros (not describing all of them, just the main ones):
#	COLOURISE:			Applies a long sed script to the output of the passed command,
#						which adds colours to the output of the various synopsys tools
#	ANALYSE:			Runs vlogan to analyse the source files
#	ELABORATE:			Runs vcs to elaborate the source files into _simv binaries
#	RUN_SIM:			Executes the simulation (See command line args below)

# Command line arguments:
#	INTERACTIVE:		running "make INTERACTIVE=1 X" will cause VCS to start up and wait for
#						user input in the UCLI. You can add breakpoints / step through, etc..
#	GUI:				running "make GUI=1 X" will start VCS with the -gui flag, opening DVE / VERDI
#	RANDOM_SEED=X:		set the random number generator's seed to X
#	DEBUG:				running "make DEBUUG=1 X" will start VCS with the -debug_acc+all argument
#						this makes it slower to run, but provides more debug information.

# Example use:
#	On the local machine (if using VCS on a remote server) run:
#		make push_to_remote
#		make connect_to_remote
#	On the remote machine:
# 		To simulate the frame_decode_tb run:
#			make frame_decode_tb
#		Then to view the coverage report in DVE run:
#			dve -dir frame_decode_tb/simv.vdb
#		To simulate in the GUI (DVE) run (make sure you have X forwarding set up):
#			make GUI=1 frame_decode_tb
#		To simulate with a specific (e.g. 1234) random seed run:
#			make RANDOM_SEED=1234 frame_decode_tb
#		To simulate in debug mode:
#			make DEBUG=1 frame_decode_tb
#	To view the reports on the local machine, on the local machine run:
# 		make pull_reports_from_remote
#		Then open frame_decode_tb/reports/dashboard.html

# ----------------------------------------------------------------------------------
# VARIABLES
# ----------------------------------------------------------------------------------

REMOTE_SERVER 	= user@server
REMOTE_PATH		= ~/desired/destination

# Directories
ROOT_DIR		= ../..

# relative to ROOT_DIR
SRC_DIR			= rtl
PKG_DIR			= $(SRC_DIR)/pkg
BFM_SRC_DIR		= verification/bfms
TB_SRC_DIR		= verification/tb
VCS_DIR			= verification/vcs

# src files
SYNTH_SRCS	= 	$(wildcard $(ROOT_DIR)/$(PKG_DIR)/*.sv) 			\
				$(wildcard $(ROOT_DIR)/$(SRC_DIR)/interfaces/*.sv) 	\
				$(wildcard $(ROOT_DIR)/$(SRC_DIR)/iso14443_2a/*.sv) \
				$(wildcard $(ROOT_DIR)/$(SRC_DIR)/iso14443_3a/*.sv) \
				$(wildcard $(ROOT_DIR)/$(SRC_DIR)/iso14443_4a/*.sv) \
				$(wildcard $(ROOT_DIR)/$(SRC_DIR)/*.sv)

# TODO: write a script to find all files and put them in the correct order
TB_BFM_SRCS =	$(wildcard $(ROOT_DIR)/$(BFM_SRC_DIR)/interfaces/*.sv) 									\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/helper/wrapper.sv											\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/helper/uid.sv												\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/helper/std_block_address.sv									\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/helper/target.sv												\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/transactions/transaction.sv									\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/transactions/queue_transaction.sv							\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/transactions/rx_bit_transaction.sv							\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/transactions/rx_byte_transaction.sv							\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/transactions/pcd_pause_n_transaction.sv						\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/transactions/tx_bit_transaction.sv							\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/transactions/tx_byte_transaction.sv							\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/transaction_generators/transaction_generator.sv				\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/transaction_converters/transaction_converter.sv				\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/transaction_converters/rx_transaction_converter.sv			\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/transaction_converters/tx_transaction_converter.sv			\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/sequences/sequence.sv										\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/sequences/specific_target_sequence.sv						\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/sequences/comms_tests_sequence.sv							\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/drivers/driver.sv 											\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/drivers/rx_iface_driver.sv 									\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/drivers/rx_bit_iface_driver.sv								\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/drivers/rx_byte_iface_driver.sv								\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/drivers/tx_iface_source_driver.sv 							\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/drivers/tx_bit_iface_source_driver.sv						\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/drivers/tx_byte_iface_source_driver.sv						\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/drivers/tx_iface_sink_driver.sv								\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/drivers/pcd_pause_n_driver.sv								\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/monitors/monitor.sv 											\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/monitors/rx_iface_monitor.sv 								\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/monitors/rx_bit_iface_monitor.sv								\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/monitors/rx_byte_iface_monitor.sv							\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/monitors/tx_iface_monitor.sv 								\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/monitors/tx_bit_iface_monitor.sv								\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/monitors/tx_byte_iface_monitor.sv							\
				$(ROOT_DIR)/$(BFM_SRC_DIR)/monitors/load_modulator_monitor.sv							\
				$(wildcard $(ROOT_DIR)/$(BFM_SRC_DIR)/analogue/*.sv)

TB_SRCS	=	$(wildcard $(ROOT_DIR)/$(TB_SRC_DIR)/*.sv) 				\
			$(wildcard $(ROOT_DIR)/$(TB_SRC_DIR)/iso14443_2a/*.sv) 	\
			$(wildcard $(ROOT_DIR)/$(TB_SRC_DIR)/iso14443_3a/*.sv)	\
			$(wildcard $(ROOT_DIR)/$(TB_SRC_DIR)/iso14443_4a/*.sv)

SRCS	= 	$(SYNTH_SRCS)	\
			$(TB_BFM_SRCS)	\
			$(TB_SRCS)

# testbenches

# This is used to generate the rules
TBS		= pause_n_latch_and_synchroniser_tb	\
		  sequence_decode_tb 				\
		  subcarrier_tb 					\
		  bit_encoder_tb 					\
		  tx_tb 							\
		  iso14443_2a_tb					\
		  frame_decode_tb 					\
		  fdt_tb 							\
		  frame_encode_tb					\
		  crc_a_tb 							\
		  crc_control_tb 					\
		  deserialiser_tb					\
		  serialiser_tb						\
		  framing_tb						\
		  initialisation_tb					\
		  routing_tb						\
		  iso14443_3a_tb					\
		  iso14443_4a_tb					\
		  iso14443a_tb

# This is for TBs that need to do something custom, it's only used for list_tbs
CUSTOM_TBS	= initialisation_tb_uid_single	\
			  initialisation_tb_uid_double	\
			  initialisation_tb_uid_triple	\
			  initialisation_tb_actual		\
			  iso14443_3a_tb_uid_single		\
			  iso14443_3a_tb_uid_double 	\
			  iso14443_3a_tb_uid_triple 	\
			  iso14443_3a_tb_actual         \
			  iso14443a_tb_uid_single       \
			  iso14443a_tb_uid_double       \
			  iso14443a_tb_uid_triple       \
			  iso14443a_tb_actual

# ----------------------------------------------------------------------------------
# colourization
# ----------------------------------------------------------------------------------
# this consists of the following colour definitions
# and three macros used to parse the stderr and stdout of commands
# ----------------------------------------------------------------------------------

# colours
COLOUR_NONE		= \x1b[0m
COLOUR_RED		= \x1b[31;01m
COLOUR_BLUE		= \x1b[34;01m
COLOUR_GREEN 	= \x1b[32;01m
COLOUR_ORANGE	= \x1b[33;01m

# Macro to generate SED command to COLOURISE output:
#	Takes two arguments:
#		1) pattern to match
#		2) colour to highlight (only highlights the matched pattern, not the whole line)
GENERATE_COLOURISE_SED = -e $$'s/$(1)/$(2)\\1$(COLOUR_NONE)/I'

# SED command to do all colour substitutions
# 	This is just a list of sed expressions generated using the GENERATE_COLOURISE_SED macro
# 	It adds the $(MORE_COLOURS) var at the end, which can be used in individual makefiles
# 	to add more colourization. IE. if you want to COLOURISE lines with Importing in them
# 	Additionally you can override COLOURISE_SED_ALL to replace all colourization options
COLOURISE_SED_ALL ?= sed -r $(call GENERATE_COLOURISE_SED,(^Error.*$$),$(COLOUR_RED)) 									\
							$(call GENERATE_COLOURISE_SED,(^.*(failed|Fatal).*$$),$(COLOUR_RED)) 						\
							$(call GENERATE_COLOURISE_SED,(^.* [1-9][0-9]* failures.*$$),$(COLOUR_RED))					\
							$(call GENERATE_COLOURISE_SED,(^.* 0 successes.*$$),$(COLOUR_BLUE))							\
							$(call GENERATE_COLOURISE_SED,(^(Warning|Lint).*$$),$(COLOUR_ORANGE)) 						\
							$(call GENERATE_COLOURISE_SED,(^Note.*$$),$(COLOUR_BLUE)) 									\
							$(call GENERATE_COLOURISE_SED,(^.* [1-9][0-9]* successes, 0 failures.*$$),$(COLOUR_GREEN))

# Actual macro that COLOURISEs
#	Takes one argument:
#		1) The command to run.
#	We run in () so that the set -o pipefail doesn't persist past this call
#	set -o pipefail makes sure our exit code is correct (ie. if vcom returns error 1, we want the entire command to return error 1)
#	We pass stderr into the above COLOURISE_SED_ALL sed command, and then redirect it back to stderr
#	Finally we pipe it in to the COLOURISE_SED_ALL again, which makes it also run on stdout
COLOURISE = (set -o pipefail; $(1) | $(COLOURISE_SED_ALL))

# ----------------------------------------------------------------------------------
# VCS macros
# ----------------------------------------------------------------------------------

# arguments to the various commands
VLOGAN_ARGS	= -full64 +lint=all +warn=all -sverilog -kdb

VCS_ARGS	= -full64 +lint=all,noSVA-DIU,noSVA-LDA,noSVA-ADORM,noSVA-NSVU,noSVA-AECASR \
			  +warn=all -assert enable_diag -ntb_opts check=all							\
			  -cm line+cond+fsm+tgl+branch+assert -kdb

ifdef DEBUG
	# full debug mode
	VCS_ARGS	+= -debug_acc+all
else
	# release mode, leave the basic debug_access on, this lets us output our assertion report
	VCS_ARGS	+= -debug_access
endif

SIMV_ARGS	= -assert global_finish_maxfail=10 -cm line+cond+fsm+tgl+branch+assert -ucli

ifdef RANDOM_SEED
	SIMV_ARGS 		+= +ntb_random_seed=$(RANDOM_SEED)
else
	SIMV_ARGS 		+= +ntb_random_seed_automatic
endif

ifdef GUI
# if we want to use the GUI then add the -gui argument to SIMV_ARGS
# and enforce interactive mode (don't run the do.tcl and don't colourise)
	SIMV_ARGS 		+= -gui
	INTERACTIVE 	= 1
endif

# the work/AN.DB dir has it's timestamp compared to the .sv files to see if we need to
# reanalyse. There may be a way to only reanalyse the necesarry files but it doesn't seem
# necesarry since it's really quick as is.
WORK_DIR	= $(VCS_DIR)/work
AN_DB_DIR	= $(ROOT_DIR)/$(WORK_DIR)/AN.DB

# The ANALYSE macro runs vlogan to analyse all the source files
# Takes zero arguments
define ANALYSE
	$(call COLOURISE, vlogan $(VLOGAN_ARGS) $(SRCS))
endef

# The ELABORATE macro runs vcs to build the simv binary for the particular testbench
# Takes one argument:
#		1) The testbench module to run
#		2) Name of the directory to put the generated files
#		3) List of additional VCS arguments, e.g. "-pvalue+WIDTH=32 -pvalue+FOO=BAR" without the quotes
define ELABORATE
	$(eval TB_NAME  = $(call strip, $(1)))
	$(eval DIR_NAME = $(call strip, $(2)))
	mkdir -p $(DIR_NAME)
	echo -e "$(COLOUR_BLUE)elaborating $(TB_NAME) with arguments $(3) as $(DIR_NAME)/simv $(COLOUR_NONE)\n"
	$(call COLOURISE, vcs $(VCS_ARGS) work.$(TB_NAME) $(3) -o $(DIR_NAME)/simv)
endef

# The RUN_SIM macro runs the simv binary produced by vcs.
# Takes one argument:
#		1) The directory containing the simv to run
# Has different behaviour depending on if we set INTERACTIVE=1 or not
# In interactive mode we don't colourise the output.
# In batch mode we run the do.tcl script
ifndef INTERACTIVE
# batch mode
define RUN_SIM
	$(eval DIR_NAME = $(call strip, $(1)))
	echo -e "$(COLOUR_BLUE)Simulating $(DIR_NAME)$(COLOUR_NONE)\n"
	$(call COLOURISE, ./$(DIR_NAME)/simv $(SIMV_ARGS) -do do.tcl)
endef
else
# interactive mode
define RUN_SIM
	$(eval DIR_NAME = $(call strip, $(1)))
	echo -e "$(COLOUR_BLUE)Simulating $(DIR_NAME)$(COLOUR_NONE)\n"
	./$(DIR_NAME)/simv $(SIMV_ARGS)
endef
endif

# ----------------------------------------------------------------------------------
# Misc macros
# ----------------------------------------------------------------------------------

# Genaretes a random number between min and max inclusive
# Takes two arguments
#	1) min
#	2) max
define RANDOM
	$(shell echo $$(( ( RANDOM % ( $(2) - $(1) + 1 ) ) + $(1) )))
endef

# ----------------------------------------------------------------------------------
# Rules / targets
# ----------------------------------------------------------------------------------

# default rule is to analyse and elaborate all files / testbenches
# elaborating all testbenches is not necesarry if you only want to run one simulation
all: analyse elaborate
.PHONY: all

# Analyse files only if any of the sources have changed more recently than the AN.DB folder
$(AN_DB_DIR): $(SRCS)
	-@rm -rf $(AN_DB_DIR)
	@echo -e "$(COLOUR_BLUE)Analysing because of changes in: $? $(COLOUR_NONE)\n"
	@$(call ANALYSE)

# Elaborate rules, of the format sequence_decode_tb/simv:
$(patsubst %,%_sim/simv,$(TBS)): $(AN_DB_DIR)
	@$(call ELABORATE, $(subst _sim/simv,,$@), $(subst /simv,,$@))

# Simulation rules
%: %_sim/simv
	@$(call RUN_SIM, $@_sim)
	@urg -dir $@_sim/simv.vdb -report $@_sim/report

# PHONY rules
analyse: $(AN_DB_DIR)
elaborate: $(patsubst %,%_sim/simv,$(TBS))

# Rule to always force making a target
.FORCE:
.PHONY: .FORCE

# TBs that override command line parameters

# These always rebuild because we want to recompile with new parameters each time
# we set UID_SIZE_CODE to 0,1,2 depending on single, double, triple.
# we set UID_INPUT_BITS to a random number, such that the number of fixed bits is 1 - 4.
# we set UID_FIXED to a random number between 0 and 15 (4 bits)
initialisation_tb_uid_single_sim/simv: $(AN_DB_DIR) .FORCE
	@$(call ELABORATE, initialisation_tb, $(subst /simv,,$@), -pvalue+initialisation_tb.UID_SIZE_CODE=0 -pvalue+initialisation_tb.UID_INPUT_BITS=$(call strip, $(call RANDOM, 28, 31)) -pvalue+initialisation_tb.UID_FIXED=$(call strip, $(call RANDOM, 0, 15)))

initialisation_tb_uid_double_sim/simv: $(AN_DB_DIR) .FORCE
	@$(call ELABORATE, initialisation_tb, $(subst /simv,,$@), -pvalue+initialisation_tb.UID_SIZE_CODE=1 -pvalue+initialisation_tb.UID_INPUT_BITS=$(call strip, $(call RANDOM, 52, 55)) -pvalue+initialisation_tb.UID_FIXED=$(call strip, $(call RANDOM, 0, 15)))

initialisation_tb_uid_triple_sim/simv: $(AN_DB_DIR) .FORCE
	@$(call ELABORATE, initialisation_tb, $(subst /simv,,$@), -pvalue+initialisation_tb.UID_SIZE_CODE=2 -pvalue+initialisation_tb.UID_INPUT_BITS=$(call strip, $(call RANDOM, 76, 79)) -pvalue+initialisation_tb.UID_FIXED=$(call strip, $(call RANDOM, 0, 15)))

iso14443_3a_tb_uid_single_sim/simv: $(AN_DB_DIR) .FORCE
	@$(call ELABORATE, iso14443_3a_tb, $(subst /simv,,$@), -pvalue+iso14443_3a_tb.UID_SIZE_CODE=0 -pvalue+iso14443_3a_tb.UID_INPUT_BITS=$(call strip, $(call RANDOM, 28, 31)) -pvalue+iso14443_3a_tb.UID_FIXED=$(call strip, $(call RANDOM, 0, 15)))

iso14443_3a_tb_uid_double_sim/simv: $(AN_DB_DIR) .FORCE
	@$(call ELABORATE, iso14443_3a_tb, $(subst /simv,,$@), -pvalue+iso14443_3a_tb.UID_SIZE_CODE=1 -pvalue+iso14443_3a_tb.UID_INPUT_BITS=$(call strip, $(call RANDOM, 52, 55)) -pvalue+iso14443_3a_tb.UID_FIXED=$(call strip, $(call RANDOM, 0, 15)))

iso14443_3a_tb_uid_triple_sim/simv: $(AN_DB_DIR) .FORCE
	@$(call ELABORATE, iso14443_3a_tb, $(subst /simv,,$@), -pvalue+iso14443_3a_tb.UID_SIZE_CODE=2 -pvalue+iso14443_3a_tb.UID_INPUT_BITS=$(call strip, $(call RANDOM, 76, 79)) -pvalue+iso14443_3a_tb.UID_FIXED=$(call strip, $(call RANDOM, 0, 15)))

iso14443a_tb_uid_single_sim/simv: $(AN_DB_DIR) .FORCE
	@$(call ELABORATE, iso14443a_tb, $(subst /simv,,$@), -pvalue+iso14443a_tb.UID_SIZE_CODE=0 -pvalue+iso14443a_tb.UID_INPUT_BITS=$(call strip, $(call RANDOM, 28, 31)) -pvalue+iso14443a_tb.UID_FIXED=$(call strip, $(call RANDOM, 0, 15)))

iso14443a_tb_uid_double_sim/simv: $(AN_DB_DIR) .FORCE
	@$(call ELABORATE, iso14443a_tb, $(subst /simv,,$@), -pvalue+iso14443a_tb.UID_SIZE_CODE=1 -pvalue+iso14443a_tb.UID_INPUT_BITS=$(call strip, $(call RANDOM, 52, 55)) -pvalue+iso14443a_tb.UID_FIXED=$(call strip, $(call RANDOM, 0, 15)))

iso14443a_tb_uid_triple_sim/simv: $(AN_DB_DIR) .FORCE
	@$(call ELABORATE, iso14443a_tb, $(subst /simv,,$@), -pvalue+iso14443a_tb.UID_SIZE_CODE=2 -pvalue+iso14443a_tb.UID_INPUT_BITS=$(call strip, $(call RANDOM, 76, 79)) -pvalue+iso14443a_tb.UID_FIXED=$(call strip, $(call RANDOM, 0, 15)))

# This test should be run with the values we want to fabricate with
# TODO: UPDATE THESE VALUES
# We use a UIDSize_SINGLE in the form of: EF FE C7 0X
# Where X is the variable part. So 4 bits variable, 28 bits fixed
# Not sure how to pass a hex value to UID_FIXED, have to pass decimal
# 0xEFFEC70 = 251653232
UID_SIZE_CODE	= 0
UID_INPUT_BITS 	= 4
UID_FIXED		= 251653232

# Don't need to rebuild these each time, as these values are fixed (should run make clean if we change them here)
initialisation_tb_actual_sim/simv: $(AN_DB_DIR)
	@$(call ELABORATE, initialisation_tb, $(subst /simv,,$@), -pvalue+initialisation_tb.UID_SIZE_CODE=$(UID_SIZE_CODE) -pvalue+initialisation_tb.UID_INPUT_BITS=$(UID_INPUT_BITS) -pvalue+initialisation_tb.UID_FIXED=$(UID_FIXED))

iso14443_3a_tb_actual_sim/simv: $(AN_DB_DIR)
	@$(call ELABORATE, iso14443_3a_tb, $(subst /simv,,$@), -pvalue+iso14443_3a_tb.UID_SIZE_CODE=$(UID_SIZE_CODE) -pvalue+iso14443_3a_tb.UID_INPUT_BITS=$(UID_INPUT_BITS) -pvalue+iso14443_3a_tb.UID_FIXED=$(UID_FIXED))

iso14443a_tb_actual_sim/simv: $(AN_DB_DIR)
	@$(call ELABORATE, iso14443a_tb, $(subst /simv,,$@), -pvalue+iso14443a_tb.UID_SIZE_CODE=$(UID_SIZE_CODE) -pvalue+iso14443a_tb.UID_INPUT_BITS=$(UID_INPUT_BITS) -pvalue+iso14443a_tb.UID_FIXED=$(UID_FIXED))

# output TBS each on it's own line
list_tbs:
	@echo $(TBS) $(CUSTOM_TBS) | sed -E 's/[ \t]+/\n/g'

# execute all TBs, pipe the result of this into a log file for easier viewing
all_tbs: $(TBS) $(CUSTOM_TBS)

clean:
	-@rm -rf *_sim/
	-@rm -rf $(ROOT_DIR)/$(WORK_DIR)
	-@rm -rf csrc/

.PHONY: analyse elaborate list_tbs all_tbs clean

# ----------------------------------------------------------------------------------
# Rules for working remotely
# ----------------------------------------------------------------------------------

# We push (overwriting all files) the src files, testbenches and the VCS dir.
# We delete any file on the server that doesn't exist locally
# except for: work/ csrc/ and *_sim/
# Which means we don't need to rebuild everything each time
push_to_remote:
	cd $(ROOT_DIR) && rsync -rRv --delete --exclude $(VCS_DIR)/work/ --exclude $(VCS_DIR)/csrc/ --exclude $(VCS_DIR)/\*_sim/ $(SRC_DIR) $(BFM_SRC_DIR) $(TB_SRC_DIR) $(VCS_DIR) $(REMOTE_SERVER):$(REMOTE_PATH)

# Pull coverage reports, this deletes existing ones
pull_reports_from_remote:
	-@rm -rf *_sim/
	rsync -rRv $(REMOTE_SERVER):$(REMOTE_PATH)/$(VCS_DIR)/./*_sim/report .

# ssh to the remote server and cd to the VCS dir
# we use -Y so we can launch graphical apps
connect_to_remote:
	ssh -Yt $(REMOTE_SERVER) "cd $(REMOTE_PATH)/$(VCS_DIR); bash"
