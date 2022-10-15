FRAMAC=../../../../bin/frama-c

TARGETS = \
  simple-main.log \
  global-initial-values.log \
  context-width.log \
  context-depth.1.log \
  context-depth.2.log \
  context-depth.3.log \
  out-of-bound.log \
  widen-hints.log \
  slevel.1.log \
  slevel.2.log \
  ilevel.1.log \
  ilevel.2.log \
	loop-unroll-const.log \
	loop-unroll-nested.log \
	loop-unroll-insuf.log \
	split-array.log \
	split-fabs.log \
	recursion-simple.log \
	recursion-imprecise.log

.SECONDEXPANSION:
.PHONY: all clean

all: $(TARGETS)
clean:
	$(RM) *.log


%.log: SOURCE = $(word 1,$(subst ., ,$*)).c
$(TARGETS) : %.log: $$(SOURCE) $(FRAMAC) $(MAKEFILE_LIST)
	$(FRAMAC) $(FCFLAGS) -eva $< > $@

global-initial-values.log: FCFLAGS += -lib-entry
context-depth%.log: FCFLAGS += -lib-entry
context-depth.2.log: FCFLAGS += -eva-context-width 1 -eva-context-depth 1
context-depth.3.log: FCFLAGS += -eva-context-width 1 -eva-context-depth 1 -eva-context-valid-pointers
slevel.1.log: FCFLAGS += -eva-slevel 55
slevel.2.log: FCFLAGS += -eva-slevel 28
ilevel.2.log: FCFLAGS += -eva-ilevel 16
split-fabs.log: FCFLAGS += -eva-domains equality
recursion-simple.log: FCFLAGS += -eva-unroll-recursive-calls 10
recursion-imprecise.log: FCFLAGS += -eva-unroll-recursive-calls 4
