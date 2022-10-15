##########################################################################
#                                                                        #
#  This file is part of Frama-C.                                         #
#                                                                        #
#  Copyright (C) 2007-2021                                               #
#    CEA (Commissariat à l'énergie atomique et aux énergies              #
#         alternatives)                                                  #
#                                                                        #
#  All rights reserved.                                                  #
#  Contact CEA LIST for licensing.                                       #
#                                                                        #
##########################################################################

include ./Makefile.config

SRC	= developer \
	introduction \
	tutorial \
	architecture \
	advance \
	refman \
	changes
SRC	:= $(addsuffix .tex, $(SRC))
SRC	+= macros.sty

GENERATED= tutorial/viewcfg/generated \
	tutorial/hello/generated \
	examples/generated/callstack.ml \
	examples/generated/use_callstack.ml \
	examples/generated/syntactic_check.ml
DEPENDENCIES= $(FRAMAC_MODERN) $(GENERATED) frama-c-book.cls

.PHONY: all check

all: developer.pdf check

FRAMAC := $(shell command -v frama-c 2> /dev/null)

# local plugin.cmi (if any) is in conflict with the one of Frama-C
check: $(GENERATED)
ifndef FRAMAC
	$(ECHO) frama-c is not installed in the PATH, nothing to check!
else
	$(ECHO) Checking compilation of example scripts
	../../bin/frama-c \
		-load-script ./examples/syntactic_check \
		-load-script ./examples/callstack \
		-load-script ./examples/use_callstack \
		-load-script ./examples/acsl_extension_foo \
		-load-script ./examples/acsl_extension_ext_types \
		-load-script ./hello_world/hello_world.ml \
       | tee check.log
	if grep -e "User Error" check.log; then \
           echo "Examples script do not compile with current Frama-C."; \
           echo "Please examine check.log and make appropriate changes"; \
           exit 1; \
        fi
	for i in value value_gui_options visitor ; \
	do ../../bin/frama-c -load-script ./tutorial/viewcfg/generated/$$i/cfg_print.ml ; \
	done
	for i in with_options with_log with_registration ; \
	do ../../bin/frama-c -load-script ./tutorial/hello/generated/$$i/hello_world.ml ; \
	done
	$(ECHO) compilation ok
	$(MAKE) -C tutorial/hello/generated/with_test
	$(MAKE) -C tutorial/hello/generated/makefile_multiple
	$(MAKE) -C tutorial/hello/generated/makefile_single
	$(MAKE) -C tutorial/viewcfg/generated/split
endif

check-all: developer.pdf 
	$(MAKE) -C ../.. check-devguide

include ../MakeLaTeXModern

developer.pdf: $(SRC) ../../VERSION $(DEPENDENCIES)
	$(MAKEPDF) developer.tex

install:
	rm -f ../manuals/plugin-development-guide.pdf
	cp developer.pdf ../manuals/plugin-development-guide.pdf

tutorial/hello/generated:
	cd tutorial/hello && make

tutorial/viewcfg/generated:
	cd tutorial/viewcfg && make

examples/generated/%.ml: examples/%.ml
	mkdir -p examples/generated
	cp $^ $@
	headache -r $@

archives: tutorial/hello/generated
	cd tutorial/hello/generated/; \
	  mv with_doc/ hello-$(VERSION)/; \
	  tar -zcvf ../../../hello-$(VERSION).tar.gz hello-$(VERSION)/*; \
	  mv hello-$(VERSION)/ with_doc/

.PHONY: tutorial/hello/generated tutorial/viewcfg/generated

###########

include $(MAKECONFIG_DIR)/Makefile.generic

###########

clean:
	rm -f *.aux *~ *.log *.blg *.bbl *.toc *.lof *.idx *.ilg *.ind
	rm -rf _whizzy* *.raux *.wdvi *.out
	rm -f *.haux *.htoc
	rm -rf $(GENERATED)

distclean dist-clean: clean
	rm -f $(filter-out mecanism.pdf, $(wildcard *.pdf))
	rm -f *.html
