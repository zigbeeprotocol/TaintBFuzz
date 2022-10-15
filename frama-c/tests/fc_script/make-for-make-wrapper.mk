# Customized makefile template for testing 'frama-c-script make-wrapper'.

include $(shell $(FRAMAC) -no-autoload-plugins -print-share-path)/analysis-scripts/prologue.mk

FCFLAGS     += \
  -kernel-warn-key annot:missing-spec=abort \
  -kernel-warn-key typing:implicit-function-declaration=abort \

EVAFLAGS    += \
  -eva-warn-key builtins:missing-spec=abort \

## Analysis targets (suffixed with .eva)
TARGETS = make-for-make-wrapper.eva

make-for-make-wrapper.parse: \
  make-wrapper.c \
  make-wrapper2.c \
  # make-wrapper3.c is deliberately absent of this list

### Epilogue. Do not modify this block. #######################################
include $(shell $(FRAMAC) -no-autoload-plugins -print-share-path)/analysis-scripts/epilogue.mk
###############################################################################
