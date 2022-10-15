.PHONY: all clean

all: main.pdf

GENERATED=biblio.bib
GENERATED+=frama-c-book.cls frama-c-cover.pdf frama-c-left.pdf frama-c-right.pdf
include ../MakeLaTeXModern

DWNLDDIR=../manuals
DOCNAME=slicing-documentation-fr.pdf

BIB_FILE = bib-slicing.bib
main.bbl : $(BIB_FILE)
	@echo "=== Fichier .bib plus récent -> effacement du .bbl"
	rm -f $(SRC).bbl

main.pdf: $(FRAMAC_MODERN) $(BIB_FILE) \
	main.tex macros_slicing.tex slicing.tex \
	intro.tex conclusion.tex \
	fonction.tex interproc.tex interproc2.tex man.tex \
	algo.tex interexples.tex intercmds.tex projets.tex \
	algoH.mli algo.ml \
	call.pdf choose_call.pdf exple2.pdf propagation.pdf propagation.pdf

###############################################################################

GENERATED+=call.pdf choose_call.pdf exple2.pdf propagation.pdf propagation.pdf
%.pdf : %.fig
	fig2dev -L pdf $< $@

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
