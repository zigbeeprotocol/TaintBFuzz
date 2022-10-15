##########################################################################
#                                                                        #
#  This file is part of Frama-C.                                         #
#                                                                        #
#  Copyright (C) 2007-2022                                               #
#    CEA (Commissariat à l'énergie atomique et aux énergies              #
#         alternatives)                                                  #
#                                                                        #
#  you can redistribute it and/or modify it under the terms of the GNU   #
#  Lesser General Public License as published by the Free Software       #
#  Foundation, version 2.1.                                              #
#                                                                        #
#  It is distributed in the hope that it will be useful,                 #
#  but WITHOUT ANY WARRANTY; without even the implied warranty of        #
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         #
#  GNU Lesser General Public License for more details.                   #
#                                                                        #
#  See the GNU Lesser General Public License version 2.1                 #
#  for more details (enclosed in the file licenses/LGPLv2.1).            #
#                                                                        #
##########################################################################

# Makefile for Frama-C/Eva case studies.
# This file is included by epilogue.mk, when using template.mk.
# See the Frama-C User Manual for more details.
#
# This Makefile uses the following variables.
#
# FRAMAC        frama-c binary
# FRAMAC_GUI    frama-c gui binary
# CPPFLAGS      preprocessing flags
# MACHDEP       machdep
# FCFLAGS       general flags to use with frama-c
# FCGUIFLAGS    flags to use with frama-c-gui
# EVAFLAGS      flags to use with the Eva plugin
# EVABUILTINS   Eva builtins to be set (via -eva-builtin)
# EVAUSESPECS   Eva functions to be overridden by specs (-eva-use-spec)
# WPFLAGS       flags to use with the WP plugin
#
# FLAMEGRAPH    If set (to any value), running an analysis will produce an
#               SVG + HTML flamegraph at the end.
#
# There are several ways to define or change these variables.
#
# With an environment variable:
#   export FRAMAC=~/bin/frama-c
#   make
#
# With command line arguments:
#   make FRAMAC=~/bin/frama-c
#
# In your Makefile, when you want to change a parameter for all analyses:
#   FCFLAGS += -verbose 2
#
# In your Makefile, for a single target :
#   target.eva: FCFLAGS += -main my_main
#
# For each analysis target, you must give the list of sources to be analyzed
# by adding them as prerequisites of target.parse, as in:
#
# target.parse: file1.c file2.c file3.c...
#

# Test if Makefile is > 4.0
ifneq (4.0,$(firstword $(sort $(MAKE_VERSION) 4.0)))
  $(error This Makefile requires Make >= 4.0 - available at http://ftp.gnu.org/gnu/make/)
endif

# Test if sed has the '--unbuffered' option (GNU sed has, but neither macOS'
# nor Busybox' have it, in which case we ignore it)
SED_UNBUFFERED:=sed$(shell sed --unbuffered //p /dev/null 2>/dev/null && echo " --unbuffered" || true)

# If there is a GNU time in the PATH, which contains the desired options
# (-f and -o), use them; otherwise, use any time (be it a shell builtin
# or a command). 'env' allows bypassing shell builtins (if they exist),
# since they usually don't have the required options.
ifeq (OK,$(shell env time -f 'test' -o '/dev/null' echo OK || echo KO))
define time_with_output
  env time -f 'user_time=%U\nmemory=%M' -o "$(1)"
endef
else
define time_with_output
  time
endef
endif

# --- Utilities ---

define display_command =
  @{
    echo '';
    [ -t 1 ] && tput setaf 4;
    echo "Command: $(strip $(1))";
    [ -t 1 ] && tput sgr0;
    echo '';
  }
endef

empty :=
space := $(empty) $(empty)
comma := ,

fc_list = $(subst $(space),$(comma),$(strip $1))


# --- Default configuration ---

FRAMAC     ?= frama-c
FRAMAC_SCRIPT = $(FRAMAC)-script
FRAMAC_GUI ?= frama-c-gui
EVAFLAGS   ?= \
  -eva-no-print -eva-no-show-progress -eva-msg-key=-initial-state \
  -eva-print-callstacks -eva-warn-key alarm=inactive \
  -no-deps-print -no-calldeps-print \
  -eva-warn-key garbled-mix \
  -calldeps -from-verbose 0 \
  $(if $(EVABUILTINS), -eva-builtin=$(call fc_list,$(EVABUILTINS)),) \
  $(if $(EVAUSESPECS), -eva-use-spec $(call fc_list,$(EVAUSESPECS)),)
WPFLAGS    ?=
FCFLAGS    ?=
FCGUIFLAGS ?=

export LIBOVERLAY_SCROLLBAR=0


# --- Cleaning ---

.PHONY: clean
clean::
	$(RM) -r *.parse *.eva

clean-backups:
	find . -regextype posix-extended \
	  -regex '^.*_[0-9]{4}-[0-9]{2}-[0-9]{2}_[0-9]{2}-[0-9]{2}-[0-9]{2}\.eva(\.(log|stats|alarms|warnings|metrics))?' \
	  -delete


# --- Generic rules ---

HR_TIMESTAMP := $(shell date +"%H:%M:%S %d/%m/%Y")# Human readable
DIR          := $(dir $(lastword $(MAKEFILE_LIST)))
SHELL        := $(shell which bash)
.SHELLFLAGS  := -eu -o pipefail -c

.ONESHELL:
.SECONDEXPANSION:
.FORCE:
.SUFFIXES: # Disable make builtins

%.parse/command %.eva/command %.wp/command:
	@#

%.parse: SOURCES = $(filter-out %/command,$^)
%.parse: PARSE = $(FRAMAC) $(FCFLAGS) $(if $(value MACHDEP),-machdep $(MACHDEP),) -cpp-extra-args="$(CPPFLAGS)" $(SOURCES)
%.parse: $$(if $$^,,.IMPOSSIBLE) $$(shell $(DIR)cmd-dep.sh $$@/command $$(PARSE))
	@$(call display_command,$(PARSE))
	mkdir -p $@
	mv -f $@/{command,running}
	{
	  $(call time_with_output,$@/stats.txt) \
	    $(PARSE) \
	      -kernel-log w:$@/warnings.log \
	      -variadic-log w:$@/warnings.log \
	      -metrics -metrics-log a:$@/metrics.log \
	      -save $@/framac.sav \
	      -print -ocode $@/framac.ast -then -no-print \
	    || ($(RM) $@/stats.txt && false) # Prevents having error code reporting in stats.txt
	} 2>&1 |
	  $(SED_UNBUFFERED) '/\[metrics\]/,999999d' |
	  tee $@/parse.log
	{
	  printf 'timestamp=%q\n' "$(HR_TIMESTAMP)";
	  printf 'warnings=%s\n' "`cat $@/warnings.log | grep ':\[kernel\]' | wc -l`";
	  printf 'cmd_args=%q\n' "$(subst ",\",$(wordlist 2,999,$(PARSE)))"
	} >> $@/stats.txt
	mv $@/{running,command}
	touch $@ # Update timestamp and prevent remake if nothing changes

%.eva: EVA = $(FRAMAC) $(FCFLAGS) -eva $(EVAFLAGS)
%.eva: PARSE_RESULT = $(word 1,$(subst ., ,$*)).parse
%.eva: $$(PARSE_RESULT) $$(shell $(DIR)cmd-dep.sh $$@/command $$(EVA)) $(if $(BENCHMARK),.FORCE,)
	@$(call display_command,$(EVA))
	mkdir -p $@
	mv -f $@/{command,running}
	{
	  $(call time_with_output,$@/stats.txt) \
	    $(EVA) \
	      -load $(PARSE_RESULT)/framac.sav -save $@/framac.sav \
	      -eva-flamegraph $@/flamegraph.txt \
	      -kernel-log w:$@/warnings.log \
	      -from-log w:$@/warnings.log \
	      -inout-log w:$@/warnings.log \
	      -scope-log w:$@/warnings.log \
	      -eva-log w:$@/warnings.log \
	      -then \
	      -report-csv $@/alarms.csv -report-no-proven \
	      -report-log w:$@/warnings.log \
	      -metrics-eva-cover \
	      -metrics-log a:$@/metrics.log \
	      -nonterm -nonterm-log a:$@/nonterm.log \
	    || ($(RM) $@/stats.txt && false) # Prevents having error code reporting in stats.txt
	} 2>&1 |
	  $(SED_UNBUFFERED) '/\[eva\] Values at end of function/,999999d' |
	  tee $@/eva.log
	$(DIR)parse-coverage.sh $@/eva.log $@/stats.txt
	{
	  printf 'timestamp=%q\n' "$(HR_TIMESTAMP)";
	  printf 'warnings=%s\n' "`cat $@/warnings.log | grep ':\[\(eva\|kernel\|from\)\]' | wc -l`";
	  printf 'alarms=%s\n' "`expr $$(cat $@/alarms.csv | wc -l) - 1`";
	  printf 'cmd_args=%q\n' "$(subst ",\",$(wordlist 2,999,$(EVA)))";
	  printf 'benchmark_tag=%s' "$(BENCHMARK)"
	} >> $@/stats.txt
	if [ ! -z $${FLAMEGRAPH+x} ]; then
	  NOGUI=1 $(FRAMAC_SCRIPT) flamegraph $@/flamegraph.txt $@/
	fi
	mv $@/{running,command}
	touch $@ # Update timestamp and prevents remake if nothing changes

%.wp: WP = $(FRAMAC) $(FCFLAGS) -wp $(WPFLAGS)
%.wp: PARSE_RESULT = $(word 1,$(subst ., ,$*)).parse
%.wp: $$(PARSE_RESULT) $$(shell $(DIR)cmd-dep.sh $$@/command $$(WP)) $(if $(BENCHMARK),.FORCE,)
	@$(call display_command,$(WP))
	mkdir -p $@
	mv -f $@/{command,running}
	{
	  $(call time_with_output,$@/stats.txt) \
	    $(WP) \
	      -load $(PARSE_RESULT)/framac.sav -save $@/framac.sav \
	      -kernel-log w:$@/warnings.log \
	      -wp-log w:$@/warnings.log \
	      -then \
	      -report-csv $@/alarms.csv -report-no-proven \
	      -report-log w:$@/warnings.log \
	    || ($(RM) $@/stats.txt && false) # Prevents having error code reporting in stats.txt
	} 2>&1 |
	  tee $@/wp.log
	{
	  printf 'timestamp=%q\n' "$(HR_TIMESTAMP)";
	  printf 'warnings=%s\n' "`cat $@/warnings.log | grep ':\[\(wp\|kernel\)\]' | wc -l`";
	  printf 'alarms=%s\n' "`expr $$(cat $@/alarms.csv | wc -l) - 1`";
	  printf 'cmd_args=%q\n' "$(subst ",\",$(wordlist 2,999,$(WP)))";
	  printf 'benchmark_tag=%s' "$(BENCHMARK)"
	} >> $@/stats.txt
	mv $@/{running,command}
	touch $@ # Update timestamp and prevent remake if nothing changes

%.gui: %
	$(FRAMAC_GUI) $(FCGUIFLAGS) -load $^/framac.sav &

# Produce and open an SVG + HTML from raw flamegraph data produced by Eva
%/flamegraph: %/flamegraph.html
	@
	case "$$OSTYPE" in
	  cygwin*) cmd /c start "$^";;
	  linux*) xdg-open "$^";;
	  darwin*) open "$^";;
	esac

%/flamegraph.html %/flamegraph.svg: %/flamegraph.txt
	NOGUI=1 $(FRAMAC_SCRIPT) flamegraph $^ $(dir $^)

.PRECIOUS: %/flamegraph.html

# clean is generally not the default goal, but if there is no default
# rule when including this file, it would be.

ifeq ($(.DEFAULT_GOAL),clean)
  .DEFAULT_GOAL :=
endif
