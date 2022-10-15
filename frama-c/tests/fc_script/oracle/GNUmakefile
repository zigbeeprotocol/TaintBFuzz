# Makefile template for Frama-C/Eva case studies.
# For details and usage information, see the Frama-C User Manual.

### Prologue. Do not modify this block. #######################################
-include path.mk # path.mk contains variables specific to each user
                 # (e.g. FRAMAC, FRAMAC_GUI) and should not be versioned. It is
                 # an optional include, unnecessary if frama-c is in the PATH.
FRAMAC ?= frama-c # FRAMAC is defined in path.mk when it is included, but the
                  # user can override it in the command-line.
ifeq ($(FRAMAC_SHARE),)
  FRAMAC_SHARE := $(shell $(FRAMAC)-config -print-share-path)
endif
include $(FRAMAC_SHARE)/analysis-scripts/prologue.mk
###############################################################################

# Edit below as needed. Suggested flags are optional.

MACHDEP = x86_64

## Preprocessing flags (for -cpp-extra-args)
CPPFLAGS    += \

## General flags
FCFLAGS     += \
  -json-compilation-database ./compile_commands.json \
  -main eva_main \
  -add-symbolic-path=.:. \
  -kernel-warn-key annot:missing-spec=abort \
  -kernel-warn-key typing:implicit-function-declaration=abort \

## Eva-specific flags
EVAFLAGS    += \
  -eva-warn-key builtins:missing-spec=abort \

## WP-specific flags
WPFLAGS    += \

## GUI-only flags
FCGUIFLAGS += \

## Analysis targets (suffixed with .eva)
TARGETS = fc_script_main.eva

### Each target <t>.eva needs a rule <t>.parse with source files as prerequisites
fc_script_main.parse: \
  fc_stubs.c \
  ./for-find-fun.c \
  ./for-find-fun2.c \
  ./main.c \
  ./main2.c \
  ./main3.c \

### Epilogue. Do not modify this block. #######################################
include $(FRAMAC_SHARE)/analysis-scripts/epilogue.mk
###############################################################################
