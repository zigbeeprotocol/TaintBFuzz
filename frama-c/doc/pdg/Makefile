.PHONY: all clean

all: main.pdf

GENERATED=biblio.bib
GENERATED+=frama-c-book.cls frama-c-cover.pdf frama-c-left.pdf frama-c-right.pdf
include ../MakeLaTeXModern

DWNLDDIR=../manuals
DOCNAME=pdg-documentation-fr.pdf
TEST_DIR=../../tests/pdg/

BIB_FILE = ../slicing/bib-slicing.bib
main.bbl : $(BIB_FILE)
	@echo "=== Fichier .bib plus récent -> effacement du .bbl"
	rm -f $(SRC).bbl

main.pdf: $(FRAMAC_MODERN) $(BIB_FILE) \
	main.tex pdg.tex macros_pdg.tex \
	intro.tex conclusion.tex \
	data.tex ctrl.tex calls.tex utilisation.tex mark.tex impact.tex \
	../images/cealistlogo.jpg \
	exple-call.c call-f.pdf call-g.pdf \
	ctrl-dpds.pdf ex-goto.pdf goto.pdf pdg-call.pdf

###############################################################################

GENERATED+=call-f.fig call-g.fig
%.fig : %.dot
	dot -Tfig $< > $@

GENERATED+=call-f.pdf call-g.pdf
%.pdf : %.fig
	fig2dev -L pdf $< $@

GENERATED+=call-f.dot call-g.dot
call-%.dot : $(TEST_DIR)/call.%.dot
	cp $< $@

call-%.dot :
	@echo
	@echo "ERROR : $@ not found : you should run PDG tests to have it"
	@echo "  Run : cd ../.. ; make pdg_tests ; cd - "
	@echo
	exit 1

GENERATED+=exple-call.c
exple-%.c : $(TEST_DIR)/%.c
	sed "1,/BDOC/d" $< > $@

###############################################################################

%.pdf: %.tex
	pdflatex $*
	bibtex $*
	pdflatex $*
	pdflatex $*

install: main.pdf
	@echo "copying main.pdf    in $(DWNLDDIR)/$(DOCNAME)"
	@rm -f "$(DWNLDDIR)/$(DOCNAME)"
	@cp main.pdf "$(DWNLDDIR)/$(DOCNAME)"

clean:
	rm -rf *~ *.aux *.log *.nav *.out *.snm *.toc *.lof *.pp *.bnf \
		*.haux  *.hbbl *.htoc \
                *.cb *.cb2 *.cm? *.bbl *.blg *.idx *.ind *.ilg \
		$(GENERATED)

###############################################################################
