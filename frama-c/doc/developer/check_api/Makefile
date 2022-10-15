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

MAKECONFIG_DIR=../../../share
include $(MAKECONFIG_DIR)/Makefile.common
include $(MAKECONFIG_DIR)/Makefile.generic

DEPENDENCIES= $(FRAMAC_MODERN) \
	frama-c-book.cls

.PHONY: check-depend clean all

all:  check_and_compare main.idx
	./check_and_compare

main.idx: ../developer.idx $(wildcard ../*.pretex)
	cp ../developer.idx main.idx

check_and_compare: check_index_grammar.cmi check_index_grammar.cmx \
	     	check_index_lexer.cmx check_and_compare.cmx 
	$(OCAMLOPT) -o check_and_compare str.cmxa check_index_grammar.cmx \
	        check_index_lexer.cmx check_and_compare.cmx 

clean:
	$(RM) *.cm*
	$(RM) check_index_*.ml
	$(RM) check_index_grammar.mli
	$(RM) *.o
	$(RM) *.output
	$(RM) check_code.annot
	$(RM) check_and_compare
	$(RM) code_file index_file summary.txt

.depend check-depend: check_index_grammar.ml check_index_lexer.ml
	ocamldep *.ml > .depend

include .depend
