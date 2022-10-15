# --------------------------------------------------------------------------
# ---  WP User & Reference Manual                                        ---
# --------------------------------------------------------------------------

.PHONY: all clean lib

all: wpcoq.pdf 

include ../MakeDoc

SHARE=../../share
COQL=Qedlib Cint Bits Cbits Cfloat Cmath Vset Memory
COQSRC=$(addprefix $(SHARE)/,$(addsuffix .v,$(COQL)))
COQSTY=$(SHARE)/doc/coq2latex.sty
COQTEX=$(SHARE)/doc/coq2latex
TEX= wpcoq.tex qed_generated.tex typed_generated.tex

lib: .lib
.lib: $(COQSRC) $(COQTEX)
	@echo "Importing $(COQL)"
	@$(COQTEX) -o "./%.tex" $(COQSRC)
	@touch .lib

$(COQTEX): $(COQTEX).mll
	make -C $(SHARE) doc/coq2latex

coq2latex.sty: $(COQSTY)
	cp -f $< .

wpcoq.pdf: $(FRAMAC_DOC) $(TEX) .lib coq2latex.sty
	rubber -d wpcoq

clean::
	rm -f .lib $(addsuffix .tex,$(COQL))