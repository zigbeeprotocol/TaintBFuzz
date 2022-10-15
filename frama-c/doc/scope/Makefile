#vide : pour ne pas utiliser de règles implicites
.SUFFIXE:
.PHONY: clean all debug

all : doc html 

logo-frama-c.eps : ../images/logo.png
	convert $< $@

logo-frama-c.pdf : ../images/logo.png
	convert $< $@

logo-inria-sophia.eps : ../images/logo-inria-sophia.eps
	cp $< $@

logo-inria-sophia.pdf : ../images/logo-inria-sophia.eps
	convert $< $@

# FIGURES_TODO = logo-frama-c logo-inria-sophia

include ../makeLatex

clean : 
