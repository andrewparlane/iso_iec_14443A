# ----------------------------------------------------------------------------------
# Tested with Synopsys VCS:
# 	vcs script version : O-2018.09
#	Compiler version = VCS-MX O-2018.09-SP2_Full64
#	VCS Build Date = Feb 28 2019 22:34:30
# On micro0.fi.uba.ar
# Make sure to have run ". /usr/synopsys2/synopsys_rc"
# 	You may need to have copied it to your local dir first
#	If you have errors with /usr/bin/ld unrecognised option -plugin
#		Then comment out the HSPICE variables source line
#	If you have other errors, make sure there's no /usr/synopsys references in
#		your PATH / other environment vars. They should all be /usr/synopsys2
# ----------------------------------------------------------------------------------

# Directories
SRC_DIR			= ../../iso14443a/hdl
PKG_DIR			= $(SRC_DIR)/pkg
TB_SRC_DIR		= ../tb
WORK_DIR		= work

# src files
SRCS	= $(wildcard $(PKG_DIR)/*.sv) \
		  $(wildcard $(SRC_DIR)/*.sv) \
		  $(wildcard $(TB_SRC_DIR)/*.sv)

# List of testbenches, these should correspond with the top level modules
# that you wish to simulate.
# Makefile rules are automatically generated to simulate build and simulate them.
# for example: make sequence_decode_tb
# You can also run in interactive mode (none GUI) with: make INTERACTIVE=1 sequence_decode_tb
TBS		= sequence_decode_tb \
		  frame_decode_tb \
		  rx_tb

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
GENERATE_COLOURISE_SED = -e $$'s/$(1)/$(2)\\1$(COLOUR_NONE)/'

# SED command to do all colour substitutions
# 	This is just a list of sed expressions generated using the GENERATE_COLOURISE_SED macro
# 	It adds the $(MORE_COLOURS) var at the end, which can be used in individual makefiles
# 	to add more colourization. IE. if you want to COLOURISE lines with Importing in them
# 	Additionally you can override COLOURISE_SED_ALL to replace all colourization options
COLOURISE_SED_ALL ?= sed -r $(call GENERATE_COLOURISE_SED,(^Error.*$$),$(COLOUR_RED)) 									\
							$(call GENERATE_COLOURISE_SED,(^Note.*$$),$(COLOUR_BLUE)) 									\
							$(call GENERATE_COLOURISE_SED,(^(Warning|Lint).*$$),$(COLOUR_ORANGE)) 						\
							$(call GENERATE_COLOURISE_SED,(^.*(failed|Fatal).*$$),$(COLOUR_RED)) 						\
							$(call GENERATE_COLOURISE_SED,(^.* 0 successes.*$$),$(COLOUR_RED))							\
							$(call GENERATE_COLOURISE_SED,(^.* [1-9][0-9]* failures.*$$),$(COLOUR_RED))					\
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

VLOGAN_ARGS	= -full64 +lint=all +warn=all -sverilog
VCS_ARGS	= -full64 +lint=all +warn=all -assert enable_diag -debug_acc+all
VSIM_ARGS	= -assert global_finish_maxfail=10 -cm assert -ucli

# Takes zero arguments
define ANALYSE
	$(call COLOURISE, vlogan $(VLOGAN_ARGS) $(SRCS))
endef

# Takes one argument:
#		1) The testbench module name to run
define ELABORATE
	$(eval TB_NAME = $(call strip, $(1)))
	echo -e "$(COLOUR_BLUE)elaborating $(TB_NAME)$(COLOUR_NONE)\n"
	$(call COLOURISE, vcs $(VCS_ARGS) work.$(TB_NAME) -o $(TB_NAME)_simv)
endef

# Takes one argument:
#		1) The testbench module name to run
# Has different behaviour depending on if we set INTERACTIVE=1 or not

ifndef INTERACTIVE
define RUN_SIM
	$(eval TB_NAME = $(call strip, $(1)))
	echo -e "$(COLOUR_BLUE)Simulating $(TB_NAME)$(COLOUR_NONE)\n"
	# batch mode,
	#	run the do.tcl
	$(call COLOURISE, ./$(TB_NAME)_simv $(VSIM_ARGS) -do do.tcl)
endef
else
define RUN_SIM
	$(eval TB_NAME = $(call strip, $(1)))
	echo -e "$(COLOUR_BLUE)Simulating $(TB_NAME)$(COLOUR_NONE)\n"
	# interactive mode
	# 	don't colourise,
	./$(TB_NAME)_simv $(VSIM_ARGS)
endef
endif

# default rule is to analyse and elaborate all files / testbenches
# elaborating all testbenches is not necesarry if you only want to run one simulation
all: analyse elaborate

.PHONY: all

# Analyse files only if any of the sources have changed more recently than the AN.DB folder
$(WORK_DIR)/AN.DB: $(SRCS)
	@echo -e "$(COLOUR_BLUE)Analysing because of changes in: $? $(COLOUR_NONE)\n"
	@$(call ANALYSE)

# Elaborate rules, of the format sequence_decode_tb_simv:
$(patsubst %,%_simv,$(TBS)): $(WORK_DIR)/AN.DB
	@$(call ELABORATE, $(subst _simv,,$@))

# Simulation rules
$(TBS): elaborate
	@$(call RUN_SIM, $@)

# PHONY rules
analyse: $(WORK_DIR)/AN.DB
elaborate: $(patsubst %,%_simv,$(TBS))

.PHONY: analyse elaborate

clean:
	-@rm ???*_simv
	-@rm -rf ???*_simv.daidir/
	-@rm -rf $(WORK_DIR)

.PHONY: clean
