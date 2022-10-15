default: all

EACSL_DIR=../..
include $(EACSL_DIR)/doc/Makefile.common

##########
# Inputs #
##########

MAIN=main
DEPS_MODERN=macros_modern.tex eacslversion.tex biblio.bib \
	intro_modern.tex speclang_modern.tex \
	libraries_modern.tex concl_modern.tex changes_modern.tex \
	term_modern.bnf binders_modern.bnf predicate_modern.bnf \
	fn_behavior_modern.bnf oldandresult_modern.bnf \
	loc_modern.bnf memory_modern.bnf list-gram.bnf \
	assertions_modern.bnf loops_modern.bnf st_contracts_modern.bnf \
	logic_modern.bnf data_invariants_modern.bnf model_modern.bnf \
	ghost_modern.bnf generalinvariants_modern.bnf iterator_modern.bnf \
	guarded_quantif_modern.bnf inductive_modern.bnf logicdecl_modern.bnf \
	higherorder_modern.bnf logictypedecl_modern.bnf logicreads_modern.bnf \
	allocation_modern.bnf abrupt_modern.bnf dependencies_modern.bnf \
	volatile-gram_modern.bnf \
	bsearch.c bsearch2.c link.c

##############
# Main rules #
##############

.PHONY: all e-acsl default
e-acsl: e-acsl-implementation.pdf e-acsl.pdf
all: e-acsl

e-acsl-implementation.pdf: $(DEPS_MODERN) $(FRAMAC_MODERN)
e-acsl-implementation.tex: $(MAIN).tex Makefile
	rm -f $@
	sed -e '/PrintRemarks/s/%--//' $^ > $@
	chmod a-w $@

e-acsl.pdf: $(DEPS_MODERN) $(FRAMAC_MODERN)
e-acsl.tex: e-acsl-implementation.tex Makefile
	rm -f $@
	sed -e '/PrintImplementationRq/s/%--//' \
	    -e '/ColorImplementationRq/s/%--//' \
	    $^ > $@
	chmod a-w $@

$(MAIN).pdf: $(DEPS_MODERN)

.PHONY: clean
clean:
	rm -rf *~ *.aux *.log *.nav *.out *.snm *.toc *.lof *.pp *.bnf \
		*.haux  *.hbbl *.htoc \
                *.cb *.cm? *.bbl *.blg *.idx *.ind *.ilg \
		transf trans.ml pp.ml pp

#########
# Tools #
#########

pp: pp.ml
	ocamlopt -o $@ str.cmxa $^

transf: transf.cmo transfmain.cmo
	ocamlc -o $@ $^

transfmain.cmo: transf.cmo
