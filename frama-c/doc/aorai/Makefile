.PHONY: all clean

DWNLDDIR=../manuals
DOCNAME=aorai-manual.pdf
ARCHIVENAME=aorai-example
EXAMPLES=example.c example.ltl example.ya \
         example_loop.c example_loop.ltl \
         example_loop2.c example_loop2.ya \
         README

BNF=ya_file.bnf basic_ya.bnf extended_ya.bnf ya_variables.bnf

all: main.pdf $(ARCHIVENAME).tgz

main.pdf: main.tex $(BNF:.bnf=.tex) macros.tex
	touch main.aux #work around latexmk bug
	latexmk -pdf main.tex

$(ARCHIVENAME).tgz: $(addprefix example/, $(EXAMPLES))
	@rm -fr $(ARCHIVENAME)
	@mkdir $(ARCHIVENAME)
	@cp $^ $(ARCHIVENAME)
	@tar czvf $@ $(ARCHIVENAME)

install: main.pdf $(ARCHIVENAME).tgz
	mkdir -p ../manuals
	@echo "copying example.tgz in ${DWNLDDIR}/$(ARCHIVENAME).tgz"
	@rm -f "${DWNLDDIR}/$(ARCHIVENAME).tgz"
	@cp $(ARCHIVENAME).tgz "${DWNLDDIR}/$(ARCHIVENAME).tgz"
	@echo "copying main.pdf    in $(DWNLDDIR)/$(DOCNAME)"
	@rm -f "$(DWNLDDIR)/$(DOCNAME)"
	@cp main.pdf "$(DWNLDDIR)/$(DOCNAME)"

clean:
	@rm -rf *~ *.aux *.log *.nav *.out *.snm *.toc \
		*.mtc* *.maf *.ist *.ilg *.ind \
		*.cm? *.idx *.o pp.ml pp *.dvi *.blg *.bbl \
		main???.png *.image.tex *.haux *.htoc *.html \
		*.backup *.pdf *.backup example/frama_c_journal.ml \
                $(ARCHIVENAME) $(ARCHIVENAME).tgz

.SUFFIXES: .tex .bnf .ml .cmo .mll

%.tex: %.bnf transf
	rm -f $@
	./transf $< > $@
	chmod a-w $@

%.ml: %.mll
	ocamllex $<

%.cmo: %.ml
	ocamlc -c $<

transf: transf.cmo
	ocamlc -o $@ $^
