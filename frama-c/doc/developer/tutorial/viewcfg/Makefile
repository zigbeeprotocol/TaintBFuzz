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

SPLIT = $(patsubst %,generated/split/cfg_%.ml,options core register gui) generated/split/Makefile
SINGLE_FILE = visitor value value_with_gui value_gui_options value_gui_state_no_clear \
		value_gui_state_clear
FINAL_PLUGINS = $(patsubst %,generated/%/cfg_print.ml,$(SINGLE_FILE)) $(SPLIT)
all: clean dirs $(FINAL_PLUGINS)

DIRS = generated $(addprefix generated/,src intermediary $(SINGLE_FILE) split)
MLIS=$(addsuffix /ViewCfg.mli,$(filter-out generated, $(DIRS)))

dirs: $(DIRS) $(MLIS)

$(DIRS): 
	mkdir -p $@

generated/src/%: src/%
	cp $< $@
	headache -r $<

generated/%/ViewCfg.mli: src/ViewCfg.mli
	cp $< $@
	headache -r $<

generated/intermediary/print_cfg_novalue.ml: generated/src/print_cfg_begin.ml\
					     generated/src/print_cfg_vfile.ml\
					     generated/src/print_cfg_vglob.ml\
					     generated/src/print_cfg_vstmt_aux_novalue.ml\
					     generated/src/print_cfg_end.ml
	rm -f $@
	for i in $^; do cat $$i >> $@; echo "" >> $@; done

generated/intermediary/print_cfg_value.ml: generated/src/print_cfg_begin.ml\
					   generated/src/print_cfg_vfile.ml\
					   generated/src/print_cfg_vglob.ml\
					   generated/src/print_cfg_vstmt_aux_value.ml\
					   generated/src/print_cfg_end.ml
	rm -f $@
	for i in $^; do cat $$i >> $@; echo "" >> $@; done

generated/intermediary/dump_function_memo_no_clear_cache_and_deps.ml:\
		 generated/src/register_cfg_graph_state.ml\
		 generated/src/dump_to_string_memoized.ml\
		 generated/src/dump_function_memo_no_clear_cache.ml	
	rm -f $@
	for i in $^; do cat $$i >> $@; echo "" >> $@; done

generated/intermediary/dump_function_memo_clear_cache_and_deps.ml:\
		 generated/src/register_cfg_graph_state.ml\
		 generated/src/dump_to_string_memoized.ml\
		 generated/src/register_value_computed_state.ml\
		 generated/src/dump_function_memo_clear_cache.ml	
	rm -f $@
	for i in $^; do cat $$i >> $@; echo "" >> $@; done



# "Final" plugins.

generated/visitor/cfg_print.ml: generated/src/print_stmt.ml\
				generated/intermediary/print_cfg_novalue.ml\
				generated/src/extend_with_simple_run.ml
	rm -f $@
	for i in $^; do cat $$i >> $@; echo "" >> $@; done

generated/value/cfg_print.ml: generated/src/print_stmt.ml\
	 		      generated/intermediary/print_cfg_value.ml\
			      generated/src/extend_with_simple_run.ml
	rm -f $@
	for i in $^; do cat $$i >> $@; echo "" >> $@; done

generated/value_with_gui/cfg_print.ml: generated/value/cfg_print.ml\
				       generated/src/dump_function.ml\
				       generated/src/gui.ml 
	rm -f $@
	for i in $^; do cat $$i >> $@; echo "" >> $@; done

generated/value_gui_options/cfg_print.ml: generated/src/print_stmt.ml\
			 		  generated/intermediary/print_cfg_value.ml\
					  generated/src/register_and_options.ml\
					  generated/src/extend_with_run_with_options.ml
	rm -f $@
	for i in $^; do cat $$i >> $@; echo "" >> $@; done

generated/value_gui_state_no_clear/cfg_print.ml:\
	   generated/src/print_stmt.ml\
	   generated/intermediary/print_cfg_value.ml\
	   generated/src/register_and_options.ml\
	   generated/src/extend_with_run_with_options.ml\
	   generated/intermediary/dump_function_memo_no_clear_cache_and_deps.ml\
	   generated/src/gui.ml
	rm -f $@
	for i in $^; do cat $$i >> $@; echo "" >> $@; done

generated/value_gui_state_clear/cfg_print.ml:\
	   generated/src/print_stmt.ml\
	   generated/intermediary/print_cfg_value.ml\
	   generated/src/register_and_options.ml\
	   generated/src/extend_with_run_with_options.ml\
	   generated/intermediary/dump_function_memo_clear_cache_and_deps.ml\
	   generated/src/gui.ml
	rm -f $@
	for i in $^; do cat $$i >> $@; echo "" >> $@; done

generated/split/cfg_options.ml:  generated/src/register_and_options.ml
	cp $^ $@

generated/split/cfg_core.ml:  generated/src/print_stmt.ml\
	 		      generated/intermediary/print_cfg_value.ml\
			      generated/src/dump_function.ml
	rm -f $@
	echo "module Options = Cfg_options" >> $@
	for i in $^; do cat $$i >> $@; echo "" >> $@; done

generated/split/cfg_register.ml: generated/src/extend_with_run_with_options.ml
	echo "open Cfg_options" > $@
	echo "open Cfg_core" >> $@
	echo "" >> $@
	for i in $^; do cat $$i >> $@; echo "" >> $@; done

generated/split/cfg_gui.ml: generated/src/gui.ml
	echo "open Cil_types" > $@
	echo "open Cfg_core" >> $@
	echo "module Options = Cfg_options" >> $@
	echo "" >> $@
	for i in $^; do cat $$i >> $@; echo "" >> $@; done

generated/split/Makefile: src/Makefile.split
	cp $^ $@

pdfs/modules.pdf: 
	cd generated/split && make doc
	cd pdfs && dot -Tpdf ../generated/split/doc/code/modules.dot -o modules.pdf



#NB: To add modules prefix, I will just use sed. e.g. sed/print_cfg/Cfg_print.print_cfg/g
#NB: Sinon, je fait des open au debut des modules; tout simplement.


# Tests

tests-no-gui: $(patsubst %,generated/%/cfg_print.ml,visitor value)
	frama-c tests/test.c -load-script generated/visitor/cfg_print.ml && cat cfg.out

	frama-c tests/test.c -val -then -load-script generated/value/cfg_print.ml && cat cfg.out
	frama-c tests/test.c -load-script generated/value/cfg_print.ml && cat cfg.out


tests-with-gui: $(patsubst %,generated/%/cfg_print.ml,value_with_gui)
#	frama-c-gui tests/test.c -val -then -load-script generated/value_with_gui/cfg_print.ml
	frama-c-gui tests/test.c -val -then -load-script generated/value_gui_options/cfg_print.ml

tests-split:
	cd generated/split && make

clean:
	rm -Rf generated
