# --------------------------------------------------------------------------
# ---  WP User & Reference Manual                                        ---
# --------------------------------------------------------------------------

.PHONY: all clean install

all: wp.pdf

include ../MakeDoc

IMAGES= \
	wp-complete.png \
	wp-gui-run.png \
	wp-unknown.png \
	wp-gui-main.png \
	wp-invalid.png \
	wp-valid.png \

TEX= \
	wp.tex \
	wp_intro.tex \
	wp_plugin.tex \
	wp_calculus.tex \
	wp_models.tex \
	wp_logic.tex \
	wp_typed.tex \
	wp_caveat.tex \
	wp_simplifier.tex \
	wp_builtins.tex \
	wp.bib

SED_DIR=tests/wp_manual/working_dir
GREP_DIR=tests/wp_manual
LOGS= swap1.log-file swap2.log-file swap3.log-file

EXAMPLES=../../${SED_DIR}/swap.c \
         ../../${SED_DIR}/swap1.h \
         ../../${SED_DIR}/swap2.h

# --------------------------------------------------------------------------
# ---  Generated Logs                                                    ---
# --------------------------------------------------------------------------

swap1.log-file: ../../${GREP_DIR}/oracle_qualif/manual.0.res.oracle
	echo "> frama-c -wp swap.c swap1.h" > $@
	cat $< | grep -v ${GREP_DIR}/manual.i | sed -e "s:${SED_DIR}/::" >> $@

swap2.log-file: ../../${GREP_DIR}/oracle_qualif/manual.1.res.oracle
	echo "> frama-c -wp -wp-rte swap.c swap2.h" > $@
	cat $< | grep -v ${GREP_DIR}/manual.i | sed -e "s:${SED_DIR}/::" >> $@

swap3.log-file: ../../${GREP_DIR}/oracle_qualif/manual.2.res.oracle
	echo "> frama-c -wp-verbose 0 [...] -then -report" > $@
	cat $< | grep -v ${GREP_DIR}/manual.i | sed -e "s:${SED_DIR}/::" >> $@

clean::
	@echo "Cleaning WP"
	rm -f $(LOGS)
	rm -f wp.pdf wp.cb wp.cb2 wp.log wp.out wp.aux wp.blg wp.bbl *~

logs: $(LOGS)
	rm -f $(LOGS) wp.pdf

wp.pdf: $(FRAMAC_DOC) $(TEX) $(LOGS) $(IMAGES) $(EXAMPLES)
	latexmk -pdf wp

INSTALL_TO=$(FRAMAC_TRUNK)/doc/manuals/wp-manual.pdf
install:
	rm -f $(INSTALL_TO)
	cp wp.pdf $(INSTALL_TO)
