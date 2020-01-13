# Some common macros and variables for use with compiling VHDL / Verilog
# using vcom / vlog which are packaged as part of QuestaSim
#-----------------------------------------------------------------------------------

# we use the bash shell, so we can use process substitution
SHELL			:= /bin/bash

# Most questasim tools require the path to the modelsim.ini file
# We have ours in the $(SIM_DIR)
MODELSIM_FLAG 	= -modelsimini $(SIM_DIR)/modelsim.ini

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

# Macro to generate SED command to colourize output:
#	Takes two arguments:
#		1) pattern to match
#		2) colour to highlight (only highlights the matched pattern, not the whole line)
GENERATE_COLOURIZE_SED = -e $$'s/$(1)/$(2)\\1$(COLOUR_NONE)/'

# SED command to do all colour substitutions
# 	This is just a list of sed expressions generated using the GENERATE_COLOURIZE_SED macro
# 	It adds the $(MORE_COLOURS) var at the end, which can be used in individual makefiles
# 	to add more colourization. IE. if you want to colourize lines with Importing in them
# 	Additionally you can override COLOURIZE_SED_ALL to replace all colourization options
COLOURIZE_SED_ALL ?= sed -r $(call GENERATE_COLOURIZE_SED,(Error:|UVM_ERROR|UVM_FATAL|Fatal:|FATAL ERROR|Error|Failure|FALLA!),$(COLOUR_RED)) \
							$(call GENERATE_COLOURIZE_SED,(Warning:|UVM_WARNING),$(COLOUR_ORANGE)) \
							$(call GENERATE_COLOURIZE_SED,(UVM_INFO|Note:),$(COLOUR_BLUE)) \
							$(call GENERATE_COLOURIZE_SED,(APROBAR!),$(COLOUR_GREEN)) \
							$(MORE_COLOURS)

# Actual macro that colourizes
#	Takes one argument:
#		1) The command to run.
#	We run in () so that the set -o pipefail doesn't persist past this call
#	set -o pipefail makes sure our exit code is correct (ie. if vcom returns error 1, we want the entire command to return error 1)
#	We pass stderr into the above COLOURIZE_SED_ALL sed command, and then redirect it back to stderr
#	Finally we pipe it in to the COLOURIZE_SED_ALL again, which makes it also run on stdout
COLOURIZE = (set -o pipefail; $(1) 2> >($(COLOURIZE_SED_ALL) >&2) | $(COLOURIZE_SED_ALL))

# ----------------------------------------------------------------------------------
# Library
# ----------------------------------------------------------------------------------
# Macros and rules for creating work dirs and mapping them to library names
# Variables:
# VLIB_NAME:		Name for this work. Defaults to work
#					if not overwritten by parent.
#
# VLIB_DIR:			Directory for this work.
# 					Defaults to $(SIM_DIR)/$(VLIB_NAME)
#					if not overwritten by parent.
#
# Rules:
#	get_vlib_dir:	echos $(VLIB_DIR) this is so we can access it from
#					outside of the projects.
#
# 	$(VLIB_DIR): 	If the vlib dir doesn't exist it is created
#
# Macros:
#	MAP_VLIB_CMD 	Map another work directory into our modelsim.ini
#					Note if you use this you may want to add a call
#					to DEL_VLIB_CMD in clean
#
#	DEL_VLIB_CMD	Deletes a library out of our modelsim.ini
# ----------------------------------------------------------------------------------

ifndef VLIB_NAME
VLIB_NAME	= work
endif

ifndef VLIB_DIR
VLIB_DIR 	= $(SIM_DIR)/$(VLIB_NAME)
endif

get_vlib_dir:
	@echo $(VLIB_DIR)

$(VLIB_DIR):
	vlib $(VLIB_DIR)
	vmap $(MODELSIM_FLAG) $(VLIB_NAME) $(VLIB_DIR)
	@echo -e "$(COLOUR_GREEN)Created the $(VLIB_DIR) library mapped to $(VLIB_NAME)$(COLOUR_NONE)\n"

vlib_clean:
	$(call DEL_VLIB_CMD, $(VLIB_NAME))

# Macro te map the work in a folder to our modelsim.ini
#	Takes two arguments:
#		1) relative folder path -
#			folder should contain a Makefile that
#			includes this helper.mk
#		2) library name to use
define MAP_VLIB_CMD
	$(eval OTHER_VLIB_DIR = $(shell make -s -C $(1) get_vlib_dir))
	vmap $(MODELSIM_FLAG) $(2) $(1)/$(OTHER_VLIB_DIR)
	@echo -e "$(COLOUR_GREEN)Mapping $(2) to $(1)/$(OTHER_VLIB_DIR)$(COLOUR_NONE)\n"
endef

# Macro te delete a lib from our modelsim.ini
#	Takes one arguments:
#		1) library name to use
define DEL_VLIB_CMD
	-vmap $(MODELSIM_FLAG) -del $(1)
endef

# ----------------------------------------------------------------------------------
# Compilation
# ----------------------------------------------------------------------------------
# Supports compiling .vhd or .sv files
#
# When we compile a file using vcom or vlog, we create a flag file
# which can be used as a dependency for each .vhd / .sv file.
# As make can compare the timestamps of the source file and the
# flag file. In older versions of questaSim vcom created a
# unique file per package/interface/module automaticaly
# however in the later versions it does not.
# ----------------------------------------------------------------------------------

# directory where we store the flags
FLAGS_DIR	= $(VLIB_DIR)/flags

# List of flags from list of sources
VHDL_FLAGS 		= $(patsubst $(SRC_DIR)/%.vhd, $(FLAGS_DIR)/%.flag, $(filter %.vhd, $(SRCS)))
VHDL_TB_FLAGS 	= $(patsubst $(TB_SRC_DIR)/%.vhd, $(FLAGS_DIR)/%.flag, $(filter %.vhd, $(TB_SRCS)))
SV_FLAGS 		= $(patsubst $(SRC_DIR)/%.sv, $(FLAGS_DIR)/%.flag, $(filter %.sv, $(SRCS)))
SV_TB_FLAGS 	= $(patsubst $(TB_SRC_DIR)/%.sv, $(FLAGS_DIR)/%.flag, $(filter %.sv, $(TB_SRCS)))

# Flags for use with vcom (vhdl compiler)
VCOM_FLAGS 			:= $(MODELSIM_FLAG) \
					   -work $(VLIB_NAME)

# Flags to use with modules we will synthesise (IE not testbenches)
NON_TB_VCOM_FLAGS	:= -check_synthesis

# Flags for use with vlog (verilog compiler)
VLOG_FLAGS 			:= $(MODELSIM_FLAG) \
					   -work $(VLIB_NAME)

# Flags to use with modules we will synthesise (IE not testbenches)
NON_TB_VLOG_FLAGS	:=

$(VHDL_FLAGS): $(FLAGS_DIR)/%.flag : $(SRC_DIR)/%.vhd
	@echo -e "$(COLOUR_BLUE)compiling $< because of changes in: $? $(COLOUR_NONE)\n"
	@$(call COLOURIZE ,vcom $(VCOM_FLAGS) $(NON_TB_VCOM_FLAGS) $<)
	@mkdir -p $(dir $@)
	@touch $@

$(VHDL_TB_FLAGS): $(FLAGS_DIR)/%.flag : $(TB_SRC_DIR)/%.vhd
	@echo -e "$(COLOUR_BLUE)compiling $< because of changes in: $? $(COLOUR_NONE)\n"
	@$(call COLOURIZE ,vcom $(VCOM_FLAGS) $<)
	@mkdir -p $(dir $@)
	@touch $@

$(SV_FLAGS): $(FLAGS_DIR)/%.flag : $(SRC_DIR)/%.sv
	@echo -e "$(COLOUR_BLUE)compiling $< because of changes in: $? $(COLOUR_NONE)\n"
	@$(call COLOURIZE ,vlog $(VLOG_FLAGS) $(NON_TB_VLOG_FLAGS) $<)
	@mkdir -p $(dir $@)
	@touch $@

$(SV_TB_FLAGS): $(FLAGS_DIR)/%.flag : $(TB_SRC_DIR)/%.sv
	@echo -e "$(COLOUR_BLUE)compiling $< because of changes in: $? $(COLOUR_NONE)\n"
	@$(call COLOURIZE ,vlog $(VLOG_FLAGS) $<)
	@mkdir -p $(dir $@)
	@touch $@

srcs: $(VLIB_DIR) $(VHDL_FLAGS) $(SV_FLAGS)
	@echo -e "$(COLOUR_GREEN)Compiled all sources.$(COLOUR_NONE)\n"

tb_srcs: $(VLIB_DIR) $(VHDL_TB_FLAGS) $(SV_TB_FLAGS)
	@echo -e "$(COLOUR_GREEN)Compiled all testbenches.$(COLOUR_NONE)\n"

# ----------------------------------------------------------------------------------
# Simulation
# ----------------------------------------------------------------------------------
#
# ----------------------------------------------------------------------------------

# sample vsim commands to log waves
VSIM_ALL_WAVES		=	-r /*
VSIM_DUT_WAVES		=	dut/*

# flags to pass to VSIM_CMD
# -error 3473 causes simulation to end if a component
# 		 	  instance isn't bound
# -error 3351 causes simulation to end if a generic is invalid
#			  probably would have to be passed over the cmd line
#			  with -g
VSIM_FLAGS					:=	$(MODELSIM_FLAG) \
								-sv_seed random \
								-error 3473 \
								-error 3351

# the run the test command, with coverage support
#	Takes three arguments:
#		1) Top level module name
#		2) Additional VSIM_FLAGS
#		3) Coverage file
define VSIM_CMD_WITH_COVERAGE
	@echo -e "$(COLOUR_GREEN)Running simulation of $(1).$(COLOUR_NONE)\n"
	@mkdir -p $(WAVES_DIR)
	# move the old coverage file to _old
	-mv $(3) $(3)_old
	# run the simulation
	$(call COLOURIZE, \
		vsim $(VSIM_FLAGS) \
			 $(2) \
			 -wlf $(WAVES_DIR)/$(strip $(1)).wlf \
			 -voptargs="+acc" \
			 -do "coverage save $(3) -onexit; \
				  set WildcardFilter {}; \
				  log -r /*; \
				  run 5 sec; \
				  assertion report -recursive *; \
				  quit -f" \
			 $(1))

	# merge the coverage file with the old one
	-vcover merge $(3) $(3) $(3)_old

	# create a link to the .wlf named last.wlf so we can use make view_last
	-ln -f $(WAVES_DIR)/$(strip $(1)).wlf $(WAVES_DIR)/last.wlf
endef

# the run the test command, using the default coverage file
#	Takes two arguments:
#		1) Top level module name
#		2) Additional VSIM_FLAGS
define VSIM_CMD
	@$(call VSIM_CMD_WITH_COVERAGE, $(1), $(2), $(SIM_DIR)/coverage.ucdb)
endef


# A macro to open questasim and show us the saved waves
#	Takes two arguments:
#		1) .wlf file path
#		2) Waves to record - see VSIM_DUT_WAVES and VSIM_ALL_WAVES for format
define VSIM_VIEW_WAVES_WLF
	@if [ ! -e $(1) ]; then \
		echo -e "$(COLOUR_RED)$(1) does not exist. $(COLOUR_NONE)\n"; \
	else \
		questasim $(MODELSIM_FLAG) \
				  -do "vsim -view $(1); \
					   set WildcardFilter {}; \
					   add wave $(2)"; \
	fi
endef

# A macro to open questasim and show us the saved waves
#	Takes two arguments:
#		1) Top level module name
#		2) Waves to record - see VSIM_DUT_WAVES and VSIM_ALL_WAVES for format
define VSIM_VIEW_WAVES_TLM
	$(eval WLF = $(WAVES_DIR)/$(strip $(1)).wlf)
	$(call VSIM_VIEW_WAVES_WLF, $(WLF), $(2))
endef


# A generic rule to open questasim and show us the saved waves
view:
	$(call VSIM_VIEW_WAVES_WLF, $(WLF), $(VSIM_ALL_WAVES))

view_last:
	$(call VSIM_VIEW_WAVES_WLF, $(WAVES_DIR)/last.wlf, $(VSIM_ALL_WAVES))

# ----------------------------------------------------------------------------------
# Coverage reporting
# ----------------------------------------------------------------------------------
#	Takes one arguments:
#		1) Coverage file
define COVERAGE_REPORT
	@echo -e "$(COLOUR_GREEN) Generating coverage report from $(1).$(COLOUR_NONE)\n"
	if [ ! -e $(1) ]; then \
		echo -e "$(COLOUR_RED)Error: file $(1) doesn't exist$(COLOUR_NONE)"; \
		exit 1; \
	else \
		vcover report -html $(1); \
	fi;
endef

# ----------------------------------------------------------------------------------
# Cleaning
# ----------------------------------------------------------------------------------

helper_clean: vlib_clean
	-rm -rf $(VLIB_DIR)

# ----------------------------------------------------------------------------------
# PHONY
# ----------------------------------------------------------------------------------

.PHONY: helper_clean vlib_clean srcs tb_srcs view view_last get_vlib_dir
