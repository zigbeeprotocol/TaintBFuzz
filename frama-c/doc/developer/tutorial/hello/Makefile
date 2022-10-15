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

PLUGIN_DIRS = script with_registration with_log makefile_single makefile_multiple with_options with_test with_doc
FINAL_PLUGINS = $(patsubst %,generated/%,$(PLUGIN_DIRS))
DIRS = generated $(addprefix generated/, src $(PLUGIN_DIRS))
MLIS=$(addsuffix /Hello.mli,$(filter-out generated, $(DIRS)))

all: clean $(FINAL_PLUGINS) $(MLIS)

generated/src/Makefile%: src/Makefile%
	mkdir -p $(dir $@)
	cp $< $@
	headache -r $<

generated/src/%.ml: src/%.ml
	mkdir -p $(dir $@)
	cp $< $@
	headache -r $<

generated/src/tests/hello/%.c: src/%.c
	mkdir -p $(dir $@)
	cp $< $@
	headache -r $<

generated/src/tests/hello/oracle/%.oracle: src/%.oracle
	mkdir -p $(dir $@)
	cp $< $@

generated/%/Hello.mli: src/Hello.mli
	mkdir -p $(dir $@)
	cp $< $@
	headache -r $<

generated/script: generated/src/run_print_to_file.ml \
                  generated/src/extend_run.ml
	mkdir -p $@
	for i in $^; do cat $$i >> $@/hello_world.ml; echo "" >> $@/hello_world.ml; done

generated/with_registration: generated/src/help_msg.ml \
                             generated/src/register.ml \
                             generated/src/run_print_to_file.ml \
                             generated/src/extend_run.ml
	mkdir -p $@
	for i in $^; do cat $$i >> $@/hello_world.ml; echo "" >> $@/hello_world.ml; done

generated/with_log: generated/src/help_msg.ml \
                    generated/src/register.ml \
                    generated/src/run_log.ml \
                    generated/src/extend_run.ml
	mkdir -p $@
	for i in $^; do cat $$i >> $@/hello_world.ml; echo "" >> $@/hello_world.ml; done

generated/with_options: generated/src/help_msg.ml \
                        generated/src/register.ml \
                        generated/src/options_enabled.ml \
                        generated/src/options_output_file.ml \
                        generated/src/run_with_options.ml \
                        generated/src/extend_run.ml \
                        generated/src/Makefile.single-file
	mkdir -p $@
	cp generated/src/Makefile.single-file $@/Makefile
	for i in $(filter-out generated/src/Makefile.single-file, $^); do \
	  cat $$i >> $@/hello_world.ml; \
	  echo "" >> $@/hello_world.ml; \
	done

generated/makefile_single: generated/with_options generated/src/Makefile.single-file
	mkdir -p $@
	cp generated/with_options/hello_world.ml $@/hello_world.ml
	cp generated/src/Makefile.single-file $@/Makefile

generated/makefile_multiple: generated/src/help_msg.ml \
                             generated/src/register.ml \
                             generated/src/options_enabled.ml \
                             generated/src/options_output_file.ml \
                             generated/src/print.ml \
                             generated/src/run_call_print.ml \
                             generated/src/extend_run.ml \
                             generated/src/Makefile.multiple-files
	mkdir -p $@
	cp generated/src/help_msg.ml $@/hello_options.ml
	echo "" >> $@/hello_options.ml
	cat generated/src/register.ml >> $@/hello_options.ml
	echo "" >> $@/hello_options.ml
	cat generated/src/options_enabled.ml >> $@/hello_options.ml
	echo "" >> $@/hello_options.ml
	cat generated/src/options_output_file.ml >> $@/hello_options.ml
	cp generated/src/print.ml $@/hello_print.ml
	cp generated/src/run_call_print.ml $@/hello_run.ml
	echo "" >> $@/hello_run.ml
	cat generated/src/extend_run.ml >> $@/hello_run.ml
	cp generated/src/Makefile.multiple-files $@/Makefile

generated/with_test: generated/src/run_call_print_bug.ml \
                     generated/src/tests/hello/hello_test.c \
                     generated/src/Makefile.test
	mkdir -p $@
	cp generated/makefile_multiple/hello_options.ml $@/hello_options.ml
	cp generated/makefile_multiple/hello_print.ml $@/hello_print.ml
	cp generated/makefile_multiple/hello_run.ml $@/hello_run.ml
	cp generated/src/run_call_print_bug.ml $@/hello_run_bug.ml
	echo "" >> $@/hello_run_bug.ml
	cat generated/src/extend_run.ml >> $@/hello_run_bug.ml
	mkdir -p $@/tests/hello
	cp generated/src/tests/hello/hello_test.c $@/tests/hello/hello_test.c
	cp generated/src/Makefile.test $@/Makefile

generated/with_doc: generated/src/help_msg.ml \
                    generated/src/register.ml \
                    generated/src/options_enabled.ml \
                    generated/src/options_output_file.ml \
                    generated/src/print.ml \
                    generated/src/run_call_print.ml \
                    generated/src/extend_run.ml \
                    generated/src/help_msg.doc.ml \
                    generated/src/register.doc.ml \
                    generated/src/options_enabled.doc.ml \
                    generated/src/options_output_file.doc.ml \
                    generated/src/print.doc.ml \
                    generated/src/run_call_print.doc.ml \
                    generated/src/extend_run.doc.ml \
                    generated/src/hello_options.doc.ml \
                    generated/src/hello_print.doc.ml \
                    generated/src/hello_run.doc.ml \
                    generated/src/tests/hello/oracle/hello_test.err.oracle \
                    generated/src/tests/hello/oracle/hello_test.res.oracle \
                    generated/src/Makefile.test
	mkdir -p $@
	cp generated/src/hello_options.doc.ml $@/hello_options.ml
	echo "" >> $@/hello_options.ml
	cat generated/src/help_msg.doc.ml >> $@/hello_options.ml
	cat generated/src/help_msg.ml >> $@/hello_options.ml
	echo "" >> $@/hello_options.ml
	cat generated/src/register.doc.ml >> $@/hello_options.ml
	cat generated/src/register.ml >> $@/hello_options.ml
	echo "" >> $@/hello_options.ml
	cat generated/src/options_enabled.doc.ml >> $@/hello_options.ml
	cat generated/src/options_enabled.ml >> $@/hello_options.ml
	echo "" >> $@/hello_options.ml
	cat generated/src/options_output_file.doc.ml >> $@/hello_options.ml
	cat generated/src/options_output_file.ml >> $@/hello_options.ml
	cp generated/src/hello_print.doc.ml $@/hello_print.ml
	echo "" >> $@/hello_print.ml
	cat generated/src/print.doc.ml >> $@/hello_print.ml
	cat generated/src/print.ml >> $@/hello_print.ml
	cp generated/src/hello_run.doc.ml $@/hello_run.ml
	echo "" >> $@/hello_run.ml
	cat generated/src/run_call_print.doc.ml >> $@/hello_run.ml
	cat generated/src/run_call_print.ml >> $@/hello_run.ml
	echo "" >> $@/hello_run.ml
	cat generated/src/extend_run.doc.ml >> $@/hello_run.ml
	cat generated/src/extend_run.ml >> $@/hello_run.ml
	mkdir -p $@/tests/hello
	cp generated/src/tests/hello/hello_test.c $@/tests/hello/hello_test.c
	mkdir -p $@/tests/hello/oracle
	cp generated/src/tests/hello/oracle/hello_test.err.oracle $@/tests/hello/oracle/hello_test.err.oracle
	cp generated/src/tests/hello/oracle/hello_test.res.oracle $@/tests/hello/oracle/hello_test.res.oracle
	cp generated/src/Makefile.test $@/Makefile

tests:
	cd generated/script && frama-c -load-script hello_world.ml && cat hello.out
	cd generated/with_registration && frama-c -load-script hello_world.ml && cat hello.out
	cd generated/with_log && frama-c -load-script hello_world.ml -hello-verbose 2
	cd generated/with_options && make && frama-c -load-module ./top/Hello
	cd generated/makefile_single && make && frama-c -load-module ./top/Hello
	cd generated/makefile_multiple && make && frama-c -load-module ./top/Hello
	cd generated/with_test && make && frama-c -load-module ./top/Hello
	cd generated/with_doc && make && frama-c -load-module ./top/Hello

clean:
	rm -Rf generated
