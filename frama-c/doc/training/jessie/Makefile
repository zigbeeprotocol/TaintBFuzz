ACSLC=mean_orig.c meansig.c 4bad1.c 4bad2.c 4good.c mean_terminates.c 6pred.c \
      mean_spec_orig.c find_array_orig.c sort_array_orig.c predicate.c \
      find_array_invariant.c find_array_variant.c find_array_assertions.c \
	find_array_contract.c 	\
      sort_inductive.c alias.c mean_res.c

all: slides.pdf handout.pdf

demo: clean
	for file in *_orig.c; do \
        sed -e '/\/\/NOPP-/d' $$file > \
             `echo $$file | sed -e 's/\(.*\)_orig.c/\1.c/'`; \
	done

clean:
	rm -f *.aux *.log *~ *.nav *.out *.snm *.toc *.vrb *.pp *.cm*
	rm -fr *.jessie

realclean: clean
	rm -f slides.pdf pp pp.ml slides.tex handout.tex handout.pdf
	for file in *_orig.c; do \
	rm -f `echo $$file | sed -e 's/\(.*\)_orig.c/\1.c/'`; \
	done

.PHONY: all clean realclean demo

.SUFFIXES: .tex .pdf .c .pp .mll .ml

.PRECIOUS: %.pp

handout.tex: slides.tex
	sed -e 's/\\documentclass\[/\\documentclass[handout,/' \
	    -e 's/\\documentclass{/\\documentclass[handout]{/' \
	    $< > $@

%.pdf: %.tex $(ACSLC:.c=.pp) gwhy.pdf
	rubber -d $<

%.tex: %.pretex pp
	./pp -color $< > $@

%.pp: %.c pp
	./pp -utf8 -color -c $< > $@

%.ml: %.mll
	ocamllex $<

pp: pp.ml
	ocamlc -o $@ str.cma $<
