JSON_OUTPUT_DIR=$(dir $(abspath $(lastword $(MAKEFILE_LIST))))json-output
PUSH_ALERTS_DIR=$(dir $(abspath $(lastword $(MAKEFILE_LIST))))push-alerts

compile:
	make -C $(JSON_OUTPUT_DIR) compile

run:
	make -C $(JSON_OUTPUT_DIR) run

launch_receiver:
	FLASK_APP=$(PUSH_ALERTS_DIR)/receiver.py FLASK_ENV=development flask run

run_wrapped: compile
	$(PUSH_ALERTS_DIR)/wrapper.py \
		--alert-url http://localhost:5000/alert \
		--id EnsuresecEE \
		--tool-id EnsuresecEE_EACSL \
		$(JSON_OUTPUT_DIR)/build/ensuresec_ee.e-acsl

run_wrapped_print_all:
	make -C $(JSON_OUTPUT_DIR) compile_print_all
	$(PUSH_ALERTS_DIR)/wrapper.py \
		--alert-url http://localhost:5000/alert \
		--id EnsuresecEE \
		--tool-id EnsuresecEE_EACSL \
		$(JSON_OUTPUT_DIR)/build/ensuresec_ee_pall.e-acsl
