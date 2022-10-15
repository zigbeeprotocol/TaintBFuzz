OUT:=$(dir $(abspath $(lastword $(MAKEFILE_LIST))))build
DEPS:=Makefile ensuresec_ee.c json_assert.c
EACSL_CC:=e-acsl-gcc.sh -c --concurrency --external-assert json_assert.c ensuresec_ee.c
MKDIR:=mkdir -p

EE_ID:=EnsuresecEE
EE_TOOL_ID:=EnsuresecEE_EACSL

$(OUT)/ensuresec_ee.e-acsl: $(DEPS)
	$(MKDIR) $(OUT)
	$(EACSL_CC) -o $(OUT)/ensuresec_ee.frama.c -O $(OUT)/ensuresec_ee

$(OUT)/ensuresec_ee_pall.e-acsl: $(DEPS)
	$(MKDIR) $(OUT)
	$(EACSL_CC) -e -DE_ACSL_DEBUG_ASSERT -o $(OUT)/ensuresec_ee_pall.frama.c -O $(OUT)/ensuresec_ee_pall

$(OUT)/ensuresec_ee_debug.e-acsl: $(DEPS)
	$(MKDIR) $(OUT)
	$(EACSL_CC) -e -DE_ACSL_DEBUG_ASSERT --rt-debug -o $(OUT)/ensuresec_ee_debug.frama.c -O $(OUT)/ensuresec_ee_debug

compile: $(OUT)/ensuresec_ee.e-acsl
compile_print_all: $(OUT)/ensuresec_ee_pall.e-acsl
compile_debug: $(OUT)/ensuresec_ee_debug.e-acsl

run: $(OUT)/ensuresec_ee.e-acsl
	ENSURESEC_EE_ID="$(EE_ID)" ENSURESEC_EE_TOOL_ID="$(EE_TOOL_ID)" ENSURESEC_OUTPUT_FILE="$(OUT)/ensuresec_ee.json" $(OUT)/ensuresec_ee.e-acsl

run_print_all: $(OUT)/ensuresec_ee_pall.e-acsl
	ENSURESEC_EE_ID="$(EE_ID)" ENSURESEC_EE_TOOL_ID="$(EE_TOOL_ID)" ENSURESEC_OUTPUT_FILE="$(OUT)/ensuresec_ee_pall.json" $(OUT)/ensuresec_ee_pall.e-acsl

run_debug: $(OUT)/ensuresec_ee_debug.e-acsl
	ENSURESEC_EE_ID="$(EE_ID)" ENSURESEC_EE_TOOL_ID="$(EE_TOOL_ID)" ENSURESEC_OUTPUT_FILE="$(OUT)/ensuresec_ee_debug.json" $(OUT)/ensuresec_ee_debug.e-acsl

all: run run_print_all run_debug

clean:
	rm -rf $(OUT)
