.PHONY: *-stripped *-gui push-*

help:
	@echo "Targets: $(TARGETS)"

##########################
# LIST OF VARIABLES IN TEMPLATE FILES, TO BE REPLACED VIA SED
# @ALPINE_BASE@
# @ALPINE_OPAM_BASE@
# @CVC4@
# @CVC4_VERSION@
# @ENV@
# @FRAMAC_TESTS@
# @GUI_ALPINE_DEPS@
# @GUI_OPAM_DEPS@
# @GUI_REMAKE@
# @OCAMLV@
# @OPAM_CACHE_FIX@
# @OPAM_DEPS@
# @OPAM_SWITCH@
# @PATCH_FRAMAC@
# @TEST_FLAGS@
# @WHY3_CONFIG@
# @WP_PROVERS@
# @WP_REPORT@
# @WP_TEST@
# @Z3@


## TEST_FLAGS:
## PTESTS_OPTS=-error-code : if all tests pass
## (nothing) : if tests compile, but fail
## || true : if tests fail to compile

push-dev: dev dev-gui dev-stripped
	docker push framac/frama-c:dev
	docker push framac/frama-c-gui:dev
	docker push framac/frama-c:dev-stripped

dev: Dockerfile.dev
	@echo "For 'dev' builds, consider adding ARGS=--no-cache to force"
	@echo "Docker to rebuild all layers."
	docker build . -t framac/frama-c:dev --target frama-c-slim -f $^ $(ARGS)

dev-gui: Dockerfile.dev
	@echo "For 'dev' builds, consider adding ARGS=--no-cache to force"
	@echo "Docker to rebuild all layers."
	docker build . -t framac/frama-c-gui:dev --target frama-c-gui-slim -f $^ $(ARGS)
TARGETS += dev-gui

dev-stripped: Dockerfile.dev
	@echo "For 'dev' builds, consider adding ARGS=--no-cache to force"
	@echo "Docker to rebuild all layers."
	docker build . -t framac/frama-c:dev-stripped --target frama-c-stripped -f $^ $(ARGS)
TARGETS += dev-stripped

release: Dockerfile.dev Dockerfile.template
	@export archive="frama-c-$$(cat ../../VERSION)-$$(cat ../../VERSION_CODENAME).tar.gz"; \
	if [ ! -e "$$archive" ]; then \
		echo "error: $$archive not found; run 'make src-distrib' and put the .tar.gz in this directory."; \
		exit 1; \
	fi; \
	docker build . -t framac/frama-c:release --target frama-c-slim --build-arg=from_archive="$$archive" -f $<
	@echo "Now run: 'docker tag framac/frama-c:release framac/frama-c:<version>'"
TARGETS += release

release-gui: Dockerfile.dev
	@echo "For 'dev' builds, consider adding ARGS=--no-cache to force"
	@echo "Docker to rebuild all layers."
	docker build . -t framac/frama-c-gui:release --target frama-c-gui-slim -f $^ $(ARGS)
	@echo "Now run: 'docker tag framac/frama-c-gui:release framac/frama-c-gui:<version>'"
TARGETS += release-gui

release-stripped: Dockerfile.dev
	@echo "For 'dev' builds, consider adding ARGS=--no-cache to force"
	@echo "Docker to rebuild all layers."
	docker build . -t framac/frama-c:release-stripped --target frama-c-stripped -f $^ $(ARGS)
	@echo "Now run: 'docker tag framac/frama-c:release-stripped framac/frama-c:<version>-stripped'"
TARGETS += release-stripped

# Note: alpine-3.14 has Z3 version 4.8.11, which is not supported in some
# versions of Why3, so we remain with alpine-3.13 for now.
Dockerfile.dev: Makefile Dockerfile.template env.template
	sed 's|@ALPINE_OPAM_BASE@|ocaml/opam:alpine-3.13-ocaml-4.08|g' Dockerfile.template | \
sed 's|@ALPINE_BASE@|alpine:3.13|g' | \
sed 's|@ENV@|$(shell cat env.template)|g' | \
sed 's|@CVC4@|$(shell cat cvc4.template)|g' | \
sed 's|@CVC4_VERSION@|1.7|g' | \
sed 's|@Z3@|$(shell cat z3.template)|g' | \
sed 's|@OPAM_CACHE_FIX@|opam repository set-url default https://opam.ocaml.org \&\&|g' | \
sed 's|@OPAM_SWITCH@|true|g' | \
sed 's|@OPAM_DEPS@|\\\
alt-ergo.2.2.0 \\\
apron.v0.9.12 \\\
conf-graphviz.0.1 \\\
mlgmpidl.1.2.12 \\\
ocamlfind.1.8.1 \\\
ocamlgraph.1.8.8 \\\
ppx_deriving_yojson.3.6.1 \\\
ppx_import.1.9.0 \\\
why3.1.5.0 \\\
yojson.1.7.0 \\\
zarith.1.10 \\\
zmq.5.1.3 \\\
conf-python-3.1.0.0 \\\
conf-time.1|' | \
sed 's|@PATCH_FRAMAC@|true|g' | \
sed 's|@WP_REPORT@|-wp -report|g'| \
sed 's|@WHY3_CONFIG@|why3 config detect|g' | \
sed 's|@WP_TEST@|frama-c -wp wp_gallery/binary-multiplication-without-overflow.c -wp-prover alt-ergo,cvc4,z3|g' | \
sed 's|@GUI_ALPINE_DEPS@||g' | \
sed 's|@GUI_OPAM_DEPS@|lablgtk3 lablgtk3-sourceview3 conf-gtksourceview3|g' | \
sed 's|@GUI_REMAKE@|make clean \&\& ./configure --enable-gui \&\& make -j \&\& sudo make install|g' | \
sed 's|@FRAMAC_TESTS@|sudo apk add ncurses \&\& cd /frama-c \&\& make tests PTESTS_OPTS=-error-code|g' | \
sed 's|@OCAMLV@|4.08|g' | \
cat > $@

24.0-stripped: Dockerfile.24.0
	docker build . -t framac/frama-c:$@ --target frama-c-stripped -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-24.0-Chromium.tar.gz $(ARGS)
TARGETS += 24.0-stripped

24.0: Dockerfile.24.0
	docker build . -t framac/frama-c:$@ --target frama-c-slim -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-24.0-Chromium.tar.gz $(ARGS)
TARGETS += 24.0

24.0-gui: Dockerfile.24.0
	docker build . -t framac/frama-c-gui:24.0 --target frama-c-gui-slim -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-24.0-Chromium.tar.gz $(ARGS)
TARGETS += 24.0-gui

push-24.0: 24.0 24.0-gui 24.0-stripped
	docker push framac/frama-c:24.0
	docker push framac/frama-c-gui:24.0
	docker push framac/frama-c:24.0-stripped

# Note: alpine-3.14 has Z3 version 4.8.11, which is not supported in some
# versions of Why3, so we remain with alpine-3.13 for now.
Dockerfile.24.0: Makefile Dockerfile.template env.template
	sed 's|@ALPINE_OPAM_BASE@|ocaml/opam:alpine-3.13-ocaml-4.08|g' Dockerfile.template | \
sed 's|@ALPINE_BASE@|alpine:3.13|g' | \
sed 's|@ENV@|$(shell cat env.template)|g' | \
sed 's|@CVC4@|$(shell cat cvc4.template)|g' | \
sed 's|@CVC4_VERSION@|1.7|g' | \
sed 's|@Z3@|$(shell cat z3.template)|g' | \
sed 's|@OPAM_CACHE_FIX@|opam repository set-url default https://opam.ocaml.org \&\&|g' | \
sed 's|@OPAM_SWITCH@|true|g' | \
sed 's|@OPAM_DEPS@|\\\
alt-ergo.2.2.0 \\\
apron.v0.9.12 \\\
conf-graphviz.0.1 \\\
mlgmpidl.1.2.12 \\\
ocamlfind.1.8.1 \\\
ocamlgraph.1.8.8 \\\
ppx_deriving_yojson.3.5.2 \\\
why3.1.4.0 \\\
yojson.1.7.0 \\\
zarith.1.9.1 \\\
zmq.5.1.3 \\\
conf-python-3.1.0.0 \\\
conf-time.1|' | \
sed 's|@PATCH_FRAMAC@|true|g' | \
sed 's|@WP_REPORT@|-wp -report|g'| \
sed 's|@WHY3_CONFIG@|why3 config detect|g' | \
sed 's|@WP_TEST@|frama-c -wp wp_gallery/binary-multiplication-without-overflow.c -wp-prover alt-ergo,cvc4,z3|g' | \
sed 's|@GUI_ALPINE_DEPS@||g' | \
sed 's|@GUI_OPAM_DEPS@|lablgtk3 lablgtk3-sourceview3 conf-gtksourceview3|g' | \
sed 's|@GUI_REMAKE@|make clean \&\& ./configure --enable-gui \&\& make -j \&\& sudo make install|g' | \
sed 's|@FRAMAC_TESTS@|sudo apk add ncurses \&\& cd /frama-c \&\& make tests PTESTS_OPTS=-error-code|g' | \
sed 's|@OCAMLV@|4.08|g' | \
cat > $@

23.1-stripped: Dockerfile.23.1
	docker build . -t framac/frama-c:$@ --target frama-c-stripped -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-23.1-Vanadium.tar.gz $(ARGS)
TARGETS += 23.1-stripped

23.1: Dockerfile.23.1
	docker build . -t framac/frama-c:$@ --target frama-c-slim -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-23.1-Vanadium.tar.gz $(ARGS)
TARGETS += 23.1

23.1-gui: Dockerfile.23.1
	docker build . -t framac/frama-c-gui:23.1 --target frama-c-gui-slim -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-23.1-Vanadium.tar.gz $(ARGS)
TARGETS += 23.1-gui

push-23.1: 23.1 23.1-gui 23.1-stripped
	docker push framac/frama-c:23.1
	docker push framac/frama-c-gui:23.1
	docker push framac/frama-c:23.1-stripped

Dockerfile.23.1: Makefile Dockerfile.template env.template
	sed 's|@ALPINE_OPAM_BASE@|ocaml/opam:alpine-3.13-ocaml-4.08|g' Dockerfile.template | \
sed 's|@ALPINE_BASE@|alpine:3.13|g' | \
sed 's|@CVC4@|$(shell cat cvc4.template)|g' | \
sed 's|@CVC4_VERSION@|1.7|g' | \
sed 's|@Z3@|$(shell cat z3.template)|g' | \
sed 's|@ENV@|$(shell cat env.template)|g' | \
sed 's|@OPAM_CACHE_FIX@||g' | \
sed 's|@OPAM_SWITCH@|true|g' | \
sed 's|@OPAM_DEPS@|\\\
alt-ergo.2.2.0 \\\
apron.v0.9.12 \\\
conf-graphviz.0.1 \\\
mlgmpidl.1.2.12 \\\
ocamlfind.1.8.1 \\\
ocamlgraph.1.8.8 \\\
ppx_deriving_yojson.3.5.2 \\\
why3.1.4.0 \\\
yojson.1.7.0 \\\
zarith.1.9.1 \\\
zmq.5.1.3 \\\
conf-python-3.1.0.0 \\\
conf-time.1|' | \
sed 's|@PATCH_FRAMAC@|true|g' | \
sed 's|@WP_REPORT@|-wp -report|g'| \
sed 's|@WHY3_CONFIG@|why3 config detect|g' | \
sed 's|@WP_TEST@|frama-c -wp wp_gallery/binary-multiplication-without-overflow.c -wp-prover alt-ergo,cvc4,Z3|g' | \
sed 's|@GUI_ALPINE_DEPS@||g'| \
sed 's|@GUI_OPAM_DEPS@|lablgtk3 lablgtk3-sourceview3 conf-gtksourceview3|g'| \
sed 's|@GUI_REMAKE@|make clean \&\& ./configure --enable-gui \&\& make -j \&\& sudo make install|g' | \
sed 's|@FRAMAC_TESTS@|sudo apk add ncurses \&\& cd /frama-c \&\& make tests|g' | \
sed 's|@OCAMLV@|4.08|g' | \
cat > $@

23.0-stripped: Dockerfile.23.0
	docker build . -t framac/frama-c:$@ --target frama-c-stripped -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-23.0-Vanadium.tar.gz $(ARGS)
TARGETS += 23.0-stripped

23.0: Dockerfile.23.0
	docker build . -t framac/frama-c:$@ --target frama-c-slim -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-23.0-Vanadium.tar.gz $(ARGS)
TARGETS += 23.0

23.0-gui: Dockerfile.23.0
	docker build . -t framac/frama-c-gui:23.0 --target frama-c-gui-slim -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-23.0-Vanadium.tar.gz $(ARGS)
TARGETS += 23.0-gui

push-23.0: 23.0 23.0-gui 23.0-stripped
	docker push framac/frama-c:23.0
	docker push framac/frama-c-gui:23.0
	docker push framac/frama-c:23.0-stripped

Dockerfile.23.0: Makefile Dockerfile.template env.template
	sed 's|@ALPINE_OPAM_BASE@|ocaml/opam:alpine-3.13-ocaml-4.08|g' Dockerfile.template | \
sed 's|@ALPINE_BASE@|alpine:3.13|g' | \
sed 's|@CVC4@|$(shell cat cvc4.template)|g' | \
sed 's|@CVC4_VERSION@|1.7|g' | \
sed 's|@Z3@|$(shell cat z3.template)|g' | \
sed 's|@ENV@|$(shell cat env.template)|g' | \
sed 's|@OPAM_CACHE_FIX@||g' | \
sed 's|@OPAM_SWITCH@|true|g' | \
sed 's|@OPAM_DEPS@|\\\
alt-ergo.2.2.0 \\\
apron.v0.9.12 \\\
conf-graphviz.0.1 \\\
mlgmpidl.1.2.12 \\\
ocamlfind.1.8.1 \\\
ocamlgraph.1.8.8 \\\
ppx_deriving_yojson.3.5.2 \\\
why3.1.4.0 \\\
yojson.1.7.0 \\\
zarith.1.9.1 \\\
zmq.5.1.3 \\\
conf-python-3.1.0.0 \\\
conf-time.1|' | \
sed 's|@PATCH_FRAMAC@|true|g' | \
sed 's|@WP_REPORT@|-wp -report|g'| \
sed 's|@WHY3_CONFIG@|why3 config detect|g' | \
sed 's|@WP_TEST@|frama-c -wp wp_gallery/binary-multiplication-without-overflow.c -wp-prover alt-ergo,cvc4,Z3|g' | \
sed 's|@GUI_ALPINE_DEPS@||g'| \
sed 's|@GUI_OPAM_DEPS@|lablgtk3 lablgtk3-sourceview3 conf-gtksourceview3|g'| \
sed 's|@GUI_REMAKE@|make clean \&\& ./configure --enable-gui \&\& make -j \&\& sudo make install|g' | \
sed 's|@FRAMAC_TESTS@|sudo apk add ncurses \&\& cd /frama-c \&\& make tests|g' | \
sed 's|@OCAMLV@|4.08|g' | \
cat > $@

22.0-stripped: Dockerfile.22.0
	docker build . -t framac/frama-c:$@ --target frama-c-stripped -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-22.0-Titanium.tar.gz $(ARGS)
TARGETS += 22.0-stripped

Dockerfile.22.0: Makefile Dockerfile.template env.template
	sed 's|@ALPINE_OPAM_BASE@|ocaml/opam:alpine-3.13-ocaml-4.08|g' Dockerfile.template | \
sed 's|@ALPINE_BASE@|alpine:3.13|g' | \
sed 's|@CVC4@|$(shell cat cvc4.template)|g' | \
sed 's|@CVC4_VERSION@|1.7|g' | \
sed 's|@Z3@|$(shell cat z3.template)|g' | \
sed 's|@ENV@|$(shell cat env.template)|g' | \
sed 's|@OPAM_CACHE_FIX@||g' | \
sed 's|@OPAM_SWITCH@|true|g' | \
sed 's|@OPAM_DEPS@|\\\
alt-ergo.2.2.0 \\\
apron.v0.9.12 \\\
conf-graphviz.0.1 \\\
mlgmpidl.1.2.12 \\\
ocamlfind.1.8.1 \\\
ocamlgraph.1.8.8 \\\
ppx_deriving_yojson.3.5.2 \\\
why3.1.3.3 \\\
yojson.1.7.0 \\\
zarith.1.9.1 \\\
zmq.5.1.3 \\\
conf-python-3.1.0.0 \\\
conf-time.1|' | \
sed 's|@PATCH_FRAMAC@|true|g' | \
sed 's|@WP_REPORT@|-wp -report|g'| \
sed 's|@WHY3_CONFIG@|why3 config --detect|g' | \
sed 's|@WP_TEST@|frama-c -wp wp_gallery/binary-multiplication-without-overflow.c -wp-prover alt-ergo,cvc4,Z3|g' | \
sed 's|@GUI_ALPINE_DEPS@||g'| \
sed 's|@GUI_OPAM_DEPS@|lablgtk3 lablgtk3-sourceview3 conf-gtksourceview3|g'| \
sed 's|@GUI_REMAKE@|make clean \&\& ./configure --enable-gui \&\& make -j \&\& sudo make install|g' | \
sed 's|@FRAMAC_TESTS@|sudo apk add ncurses \&\& cd /frama-c \&\& make tests|g' | \
sed 's|@OCAMLV@|4.08|g' | \
cat > $@

21.1-stripped: Dockerfile.21.1
	docker build . -t framac/frama-c:$@ --target frama-c-stripped -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-21.1-Scandium.tar.gz $(ARGS)
TARGETS += 21.1-stripped

Dockerfile.21.1: Makefile Dockerfile.template env.template
	sed 's|@ALPINE_OPAM_BASE@|ocaml/opam:alpine-3.13-ocaml-4.07|g' Dockerfile.template | \
sed 's|@ALPINE_BASE@|alpine:3.13|g' | \
sed 's|@CVC4@|$(shell cat cvc4.template)|g' | \
sed 's|@CVC4_VERSION@|1.7|g' | \
sed 's|@Z3@|$(shell cat z3.template)|g' | \
sed 's|@ENV@|$(shell cat env.template)|g' | \
sed 's|@OPAM_CACHE_FIX@||g' | \
sed 's|@OPAM_SWITCH@|true|g' | \
sed 's|@OPAM_DEPS@|\\\
alt-ergo.2.0.0 \\\
apron.v0.9.12 \\\
conf-graphviz.0.1 \\\
mlgmpidl.1.2.12 \\\
ocamlfind.1.8.0 \\\
ocamlgraph.1.8.8 \\\
ppx_deriving_yojson.3.5.2 \\\
why3.1.3.1 \\\
yojson.1.7.0 \\\
zarith.1.9.1 \\\
zmq.5.1.3 \\\
conf-python-3.1.0.0 \\\
conf-time.1|' | \
sed 's|@PATCH_FRAMAC@|true|g' | \
sed 's|@WP_REPORT@|-wp -report|g'| \
sed 's|@WHY3_CONFIG@|why3 config --full-config|g' | \
sed 's|@WP_TEST@|frama-c -wp wp_gallery/binary-multiplication-without-overflow.c -wp-prover alt-ergo,cvc4,Z3|g' | \
sed 's|@GUI_ALPINE_DEPS@||g'| \
sed 's|@GUI_OPAM_DEPS@|lablgtk3 lablgtk3-sourceview3 conf-gtksourceview3|g'| \
sed 's|@GUI_REMAKE@|make clean \&\& ./configure --enable-gui \&\& make -j \&\& sudo make install|g' | \
sed 's|@FRAMAC_TESTS@|sudo apk add ncurses \&\& cd /frama-c \&\& make tests|g' | \
sed 's|@OCAMLV@|4.07|g' | \
cat > $@

# Note: Frama-C 20.0 and older do not work with GCC >= 10 due to issue with
# handling of Unicode characters
20.0-stripped: Dockerfile.20.0
	docker build . -t framac/frama-c:$@ --target frama-c-stripped -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-20.0-Calcium.tar.gz $(ARGS)
TARGETS += 20.0-stripped

# Note: cairo2.0.6.1 is used for the GUI because the 0.6.2 requires 'dune-configurator'
Dockerfile.20.0: Makefile Dockerfile.template env.template
	sed 's|@ALPINE_OPAM_BASE@|ocaml/opam:alpine-3.12-ocaml-4.05|g' Dockerfile.template | \
sed 's|@ALPINE_BASE@|alpine:3.12|g' | \
sed 's|@CVC4@|$(shell cat cvc4.template)|g' | \
sed 's|@CVC4_VERSION@|1.6|g' | \
sed 's|@Z3@|$(shell cat z3.template)|g' | \
sed 's|@ENV@|$(shell cat env.template)|g' | \
sed 's|@OPAM_CACHE_FIX@|git -C /home/opam/opam-repository pull origin master \&\& |g' | \
sed 's|@OPAM_SWITCH@|true|g' | \
sed 's|@OPAM_DEPS@|\\\
alt-ergo.2.0.0 \\\
apron.20160125 \\\
conf-graphviz.0.1 \\\
mlgmpidl.1.2.11 \\\
ocamlfind.1.8.0 \\\
ocamlgraph.1.8.8 \\\
ppx_deriving_yojson.3.5.2 \\\
why3.1.2.0 \\\
yojson.1.7.0 \\\
zarith.1.9.1 \\\
zmq.5.1.3 \\\
conf-python-3.1.0.0 \\\
conf-time.1|' | \
sed 's|@PATCH_FRAMAC@|true|g' | \
sed 's|@WP_REPORT@|-wp -report|g'| \
sed 's|@WHY3_CONFIG@|why3 config --detect-provers|g' | \
sed 's|@WP_TEST@|frama-c -wp wp_gallery/binary-multiplication-without-overflow.c -wp-prover alt-ergo,cvc4,Z3|g' | \
sed 's|@GUI_ALPINE_DEPS@||g'| \
sed 's|@GUI_OPAM_DEPS@|cairo2.0.6.1 lablgtk3 lablgtk3-sourceview3 conf-gtksourceview3|g'| \
sed 's|@GUI_REMAKE@|make clean \&\& ./configure --enable-gui \&\& make -j \&\& sudo make install|g' | \
sed 's|@FRAMAC_TESTS@|sudo apk add ncurses \&\& cd /frama-c \&\& make tests \|\| true |g' | \
sed 's|@OCAMLV@|4.05|g' | \
cat > $@

19.1-stripped: Dockerfile.19.1
	docker build . -t framac/frama-c:$@ --target frama-c-stripped -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-19.1-Potassium.tar.gz $(ARGS)
TARGETS += 19.1-stripped

Dockerfile.19.1: Makefile Dockerfile.template env.template
	sed 's|@ALPINE_OPAM_BASE@|ocaml/opam:alpine-3.12-ocaml-4.05|g' Dockerfile.template | \
sed 's|@ALPINE_BASE@|alpine:3.12|g' | \
sed 's|@CVC4@|$(shell cat cvc4.template)|g' | \
sed 's|@CVC4_VERSION@|1.6|g' | \
sed 's|@Z3@|$(shell cat z3.template)|g' | \
sed 's|@ENV@|$(shell cat env.template)|g' | \
sed 's|@OPAM_CACHE_FIX@|git -C /home/opam/opam-repository pull origin master \&\& |g' | \
sed 's|@OPAM_SWITCH@|true|g' | \
sed 's|@OPAM_DEPS@|\\\
alt-ergo-free.2.0.0 \\\
apron.20160125 \\\
conf-graphviz.0.1 \\\
mlgmpidl.1.2.9 \\\
ocamlfind.1.8.0 \\\
ocamlgraph.1.8.8 \\\
ppx_deriving_yojson.3.5.2 \\\
why3.1.2.0 \\\
yojson.1.7.0 \\\
zarith.1.7 \\\
conf-python-3.1.0.0 \\\
conf-time.1|' | \
sed 's|@PATCH_FRAMAC@|true|g' | \
sed 's|@WP_REPORT@|-wp -report|g'| \
sed 's|@WHY3_CONFIG@|why3 config --detect-provers|g' | \
sed 's|@WP_TEST@|frama-c -wp wp_gallery/binary-multiplication-without-overflow.c -wp-prover alt-ergo,cvc4,Z3|g' | \
sed 's|@GUI_ALPINE_DEPS@||g'| \
sed 's|@GUI_OPAM_DEPS@|cairo2.0.6.1 lablgtk3 lablgtk3-sourceview3 conf-gtksourceview3|g'| \
sed 's|@GUI_REMAKE@|make clean \&\& ./configure --enable-gui \&\& make -j \&\& sudo make install|g' | \
sed 's|@FRAMAC_TESTS@|sudo apk add ncurses \&\& cd /frama-c \&\& make tests \|\| true|g' | \
sed 's|@OCAMLV@|4.05|g' | \
cat > $@

18.0-stripped: Dockerfile.18.0
	docker build . -t framac/frama-c:$@ --target frama-c-stripped -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-18.0-Argon.tar.gz $(ARGS)
TARGETS += 18.0-stripped

Dockerfile.18.0: Makefile Dockerfile.template env.template
	sed 's|@ALPINE_OPAM_BASE@|ocaml/opam:alpine-3.12-ocaml-4.05|g' Dockerfile.template | \
sed 's|@ALPINE_BASE@|alpine:3.12|g' | \
sed 's|@CVC4@|$(shell cat cvc4.template)|g' | \
sed 's|@CVC4_VERSION@|1.5|g' | \
sed 's|@Z3@|$(shell cat z3.template)|g' | \
sed 's|@ENV@|$(shell cat env.template)|g' | \
sed 's|@OPAM_CACHE_FIX@|git -C /home/opam/opam-repository pull origin master \&\& |g' | \
sed 's|@OPAM_SWITCH@|true|g' | \
sed 's|@OPAM_DEPS@|\\\
alt-ergo.1.30 \\\
apron.20160125 \\\
conf-graphviz.0.1 \\\
mlgmpidl.1.2.7 \\\
ocamlfind.1.8.0 \\\
ocamlgraph.1.8.8 \\\
why3.0.88.3 \\\
yojson.1.7.0 \\\
zarith.1.7 \\\
conf-python-3.1.0.0 \\\
conf-time.1|' | \
sed 's|@PATCH_FRAMAC@|true|g' | \
sed 's|@WP_REPORT@|-wp -report|g'| \
sed 's|@WHY3_CONFIG@|why3 config --detect-provers|g' | \
sed 's|@WP_TEST@|frama-c -wp wp_gallery/binary-multiplication-without-overflow.c -wp-prover alt-ergo,cvc4,Z3|g' | \
sed 's|@GUI_ALPINE_DEPS@|libart-lgpl-dev|g'| \
sed 's|@GUI_OPAM_DEPS@|cairo2.0.6.1 lablgtk conf-gnomecanvas conf-gtksourceview|g'| \
sed 's|@GUI_REMAKE@|make clean \&\& ./configure --enable-gui \&\& make -j \&\& sudo make install|g' | \
sed 's|@FRAMAC_TESTS@|sudo apk add ncurses \&\& cd /frama-c \&\& make tests \|\| true|g' | \
sed 's|@OCAMLV@|4.05|g' | \
cat > $@

17.1-stripped: Dockerfile.17.1
	docker build . -t framac/frama-c:$@ --target frama-c-stripped -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-Chlorine-20180502.tar.gz $(ARGS)
TARGETS += 17.1-stripped

# frama-c-script is not shipped from here on, so no need for conf-python
Dockerfile.17.1: Makefile Dockerfile.template env.template
	sed 's|@ALPINE_OPAM_BASE@|ocaml/opam:alpine-3.12-ocaml-4.05|g' Dockerfile.template | \
sed 's|@ALPINE_BASE@|alpine:3.12|g' | \
sed 's|@CVC4@|$(shell cat cvc4.template)|g' | \
sed 's|@CVC4_VERSION@|1.5|g' | \
sed 's|@Z3@|$(shell cat z3.template)|g' | \
sed 's|@ENV@|$(shell cat env.template)|g' | \
sed 's|@OPAM_CACHE_FIX@|git -C /home/opam/opam-repository pull origin master \&\& |g' | \
sed 's|@OPAM_SWITCH@|true|g' | \
sed 's|@OPAM_DEPS@|\\\
alt-ergo.1.30 \\\
apron.20160125 \\\
conf-graphviz.0.1 \\\
mlgmpidl.1.2.7 \\\
ocamlfind.1.8.0 \\\
ocamlgraph.1.8.8 \\\
why3.0.88.3 \\\
yojson.1.7.0 \\\
zarith.1.7 \\\
conf-time.1|' | \
sed 's|@PATCH_FRAMAC@|true|g' | \
sed 's|@WP_REPORT@|-wp -report|g'| \
sed 's|@WHY3_CONFIG@|why3 config --detect-provers|g' | \
sed 's|@WP_TEST@|frama-c -wp wp_gallery/binary-multiplication-without-overflow.c -wp-prover alt-ergo,cvc4,Z3|g' | \
sed 's|@GUI_ALPINE_DEPS@|libart-lgpl-dev|g'| \
sed 's|@GUI_OPAM_DEPS@|cairo2.0.6.1 lablgtk conf-gnomecanvas conf-gtksourceview|g'| \
sed 's|@GUI_REMAKE@|make clean \&\& ./configure --enable-gui \&\& make -j \&\& sudo make install|g' | \
sed 's|@FRAMAC_TESTS@|cd /frama-c \&\& make tests \|\| true|g' | \
sed 's|@OCAMLV@|4.05|g' | \
cat > $@

16.0-stripped: Dockerfile.16.0
	docker build . -t framac/frama-c:$@ --target frama-c-stripped -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-Sulfur-20171101.tar.gz $(ARGS)
TARGETS += 16.0-stripped

# yojson is no longer marked in the opam depends from here on
Dockerfile.16.0: Makefile Dockerfile.template env.template
	sed 's|@ALPINE_OPAM_BASE@|ocaml/opam:alpine-3.12-ocaml-4.05|g' Dockerfile.template | \
sed 's|@ALPINE_BASE@|alpine:3.12|g' | \
sed 's|@CVC4@|$(shell cat cvc4.template)|g' | \
sed 's|@CVC4_VERSION@|1.5|g' | \
sed 's|@Z3@|$(shell cat z3.template)|g' | \
sed 's|@ENV@|$(shell cat env.template)|g' | \
sed 's|@OPAM_CACHE_FIX@|git -C /home/opam/opam-repository pull origin master \&\& |g' | \
sed 's|@OPAM_SWITCH@|true|g' | \
sed 's|@OPAM_DEPS@|\\\
alt-ergo.1.30 \\\
apron.20160125 \\\
conf-graphviz.0.1 \\\
mlgmpidl.1.2.7 \\\
ocamlfind.1.8.0 \\\
ocamlgraph.1.8.8 \\\
why3.0.88.3 \\\
zarith.1.7 \\\
conf-time.1|' | \
sed 's|@PATCH_FRAMAC@|true|g' | \
sed 's|@WP_REPORT@|-wp -report|g'| \
sed 's|@WHY3_CONFIG@|why3 config --detect-provers|g' | \
sed 's|@WP_TEST@|frama-c -wp wp_gallery/binary-multiplication-without-overflow.c -wp-prover alt-ergo,cvc4,Z3|g' | \
sed 's|@GUI_ALPINE_DEPS@|libart-lgpl-dev|g'| \
sed 's|@GUI_OPAM_DEPS@|cairo2.0.6.1 lablgtk conf-gnomecanvas conf-gtksourceview|g'| \
sed 's|@GUI_REMAKE@|make clean \&\& ./configure --enable-gui \&\& make -j \&\& sudo make install|g' | \
sed 's|@FRAMAC_TESTS@|cd /frama-c \&\& make tests \|\| true|g' | \
sed 's|@OCAMLV@|4.05|g' | \
cat > $@

15.0-stripped: Dockerfile.15.0
	docker build . -t framac/frama-c:$@ --target frama-c-stripped -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-Phosphorus-20170501.tar.gz $(ARGS)
TARGETS += 15.0-stripped

Dockerfile.15.0: Makefile Dockerfile.template env.template
	sed 's|@ALPINE_OPAM_BASE@|ocaml/opam:alpine-3.12-ocaml-4.02|g' Dockerfile.template | \
sed 's|@ALPINE_BASE@|alpine:3.12|g' | \
sed 's|@CVC4@|$(shell cat cvc4.template)|g' | \
sed 's|@CVC4_VERSION@|1.5|g' | \
sed 's|@Z3@|$(shell cat z3.template)|g' | \
sed 's|@ENV@|$(shell cat env.template)|g' | \
sed 's|@OPAM_CACHE_FIX@|git -C /home/opam/opam-repository pull origin master \&\& |g' | \
sed 's|@OPAM_SWITCH@|true|g' | \
sed 's|@OPAM_DEPS@|\\\
alt-ergo.1.30 \\\
apron.20160125 \\\
conf-graphviz.0.1 \\\
mlgmpidl.1.2.7 \\\
ocamlfind.1.8.0 \\\
ocamlgraph.1.8.8 \\\
why3.0.88.3 \\\
zarith.1.7 \\\
conf-time.1|' | \
sed 's|@PATCH_FRAMAC@|true|g' | \
sed 's|@WP_REPORT@|-wp -report|g'| \
sed 's|@WHY3_CONFIG@|why3 config --detect-provers|g' | \
sed 's|@WP_TEST@|frama-c -wp wp_gallery/binary-multiplication-without-overflow.c -wp-prover alt-ergo,cvc4,Z3|g' | \
sed 's|@GUI_ALPINE_DEPS@|libart-lgpl-dev|g'| \
sed 's|@GUI_OPAM_DEPS@|cairo2.0.6.1 lablgtk conf-gnomecanvas conf-gtksourceview|g'| \
sed 's|@GUI_REMAKE@|make clean \&\& ./configure --enable-gui \&\& make -j \&\& sudo make install|g' | \
sed 's|@FRAMAC_TESTS@|cd /frama-c \&\& make tests \|\| true|g' | \
sed 's|@OCAMLV@|4.02|g' | \
cat > $@

14.0-stripped: Dockerfile.14.0
	docker build . -t framac/frama-c:$@ --target frama-c-stripped -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-Silicon-20161101.tar.gz $(ARGS)
TARGETS += 14.0-stripped

Dockerfile.14.0: Makefile Dockerfile.template env.template
	sed 's|@ALPINE_OPAM_BASE@|ocaml/opam:alpine-3.12-ocaml-4.02|g' Dockerfile.template | \
sed 's|@ALPINE_BASE@|alpine:3.12|g' | \
sed 's|@CVC4@|$(shell cat cvc4.template)|g' | \
sed 's|@CVC4_VERSION@|1.5|g' | \
sed 's|@Z3@|$(shell cat z3.template)|g' | \
sed 's|@ENV@|$(shell cat env.template)|g' | \
sed 's|@OPAM_CACHE_FIX@|git -C /home/opam/opam-repository pull origin master \&\& |g' | \
sed 's|@OPAM_SWITCH@|true|g' | \
sed 's|@OPAM_DEPS@|\\\
alt-ergo.1.30 \\\
apron.20160125 \\\
conf-graphviz.0.1 \\\
mlgmpidl.1.2.7 \\\
ocamlfind.1.8.0 \\\
ocamlgraph.1.8.8 \\\
why3.0.88.3 \\\
zarith.1.7 \\\
conf-time.1|' | \
sed 's|@PATCH_FRAMAC@|true|g' | \
sed 's|@WP_REPORT@|-wp -report|g'| \
sed 's|@WHY3_CONFIG@|why3 config --detect-provers|g' | \
sed 's#@WP_TEST@#! ( frama-c -wp wp_usage/reads.i -wp-timeout 1 -wp-prover alt-ergo,CVC4,Z3 | grep "No prover" )#g' | \
sed 's|@GUI_ALPINE_DEPS@|libart-lgpl-dev|g'| \
sed 's|@GUI_OPAM_DEPS@|cairo2.0.6.1 lablgtk conf-gnomecanvas conf-gtksourceview|g'| \
sed 's|@GUI_REMAKE@|make clean \&\& ./configure --enable-gui \&\& make -j \&\& sudo make install|g' | \
sed 's|@FRAMAC_TESTS@|cd /frama-c \&\& make tests \|\| true|g' | \
sed 's|@OCAMLV@|4.02|g' | \
cat > $@

13.0-stripped: Dockerfile.13.0
	docker build . -t framac/frama-c:$@ --target frama-c-stripped -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-Aluminium-20160502.tar.gz $(ARGS)
TARGETS += 13.0-stripped

Dockerfile.13.0: Makefile Dockerfile.template env.template
	sed 's|@ALPINE_OPAM_BASE@|ocaml/opam:alpine-3.12-ocaml-4.02|g' Dockerfile.template | \
sed 's|@ALPINE_BASE@|alpine:3.12|g' | \
sed 's|@CVC4@|$(shell cat cvc4.template)|g' | \
sed 's|@CVC4_VERSION@|1.5|g' | \
sed 's|@Z3@|$(shell cat z3.template)|g' | \
sed 's|@ENV@|$(shell cat env.template)|g' | \
sed 's|@OPAM_CACHE_FIX@|git -C /home/opam/opam-repository pull origin master \&\& |g' | \
sed 's|@OPAM_SWITCH@|true|g' | \
sed 's|@OPAM_DEPS@|\\\
alt-ergo.1.30 \\\
apron.20160125 \\\
conf-graphviz.0.1 \\\
mlgmpidl.1.2.7 \\\
ocamlfind.1.8.0 \\\
ocamlgraph.1.8.8 \\\
why3.0.88.3 \\\
zarith.1.7 \\\
conf-time.1|' | \
sed 's|@PATCH_FRAMAC@|true|g' | \
sed 's|@WP_REPORT@|-wp -report|g'| \
sed 's|@WHY3_CONFIG@|why3 config --detect-provers|g' | \
sed 's#@WP_TEST@#! ( frama-c -wp wp_usage/reads.i -wp-timeout 1 -wp-prover alt-ergo,CVC4,Z3 | grep "No prover" )#g' | \
sed 's|@GUI_ALPINE_DEPS@|libart-lgpl-dev|g'| \
sed 's|@GUI_OPAM_DEPS@|cairo2.0.6.1 lablgtk conf-gnomecanvas conf-gtksourceview|g'| \
sed 's|@GUI_REMAKE@|make clean \&\& ./configure --enable-gui \&\& make -j \&\& sudo make install|g' | \
sed 's|@FRAMAC_TESTS@|cd /frama-c \&\& make tests \|\| true|g' | \
sed 's|@OCAMLV@|4.02|g' | \
cat > $@

12.0-stripped: Dockerfile.12.0
	docker build . -t framac/frama-c:$@ --target frama-c-stripped -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-Magnesium-20151002.tar.gz $(ARGS)
TARGETS += 12.0-stripped

# apron is not shipped with Frama-C, from here on
Dockerfile.12.0: Makefile Dockerfile.template env.template
	sed 's|@ALPINE_OPAM_BASE@|ocaml/opam:alpine-3.12-ocaml-4.02|g' Dockerfile.template | \
sed 's|@ALPINE_BASE@|alpine:3.12|g' | \
sed 's|@CVC4@|$(shell cat cvc4.template)|g' | \
sed 's|@CVC4_VERSION@|1.5|g' | \
sed 's|@Z3@|$(shell cat z3.template)|g' | \
sed 's|@ENV@|$(shell cat env.template)|g' | \
sed 's|@OPAM_CACHE_FIX@|git -C /home/opam/opam-repository pull origin master \&\& |g' | \
sed 's|@OPAM_SWITCH@|true|g' | \
sed 's|@OPAM_DEPS@|\\\
alt-ergo.1.30 \\\
conf-graphviz.0.1 \\\
ocamlfind.1.8.0 \\\
ocamlgraph.1.8.8 \\\
why3.0.88.3 \\\
zarith.1.7 \\\
conf-time.1|' | \
sed 's|@PATCH_FRAMAC@|true|g' | \
sed 's|@WP_REPORT@|-wp -report|g'| \
sed 's|@WHY3_CONFIG@|why3 config --detect-provers|g' | \
sed 's#@WP_TEST@#! ( frama-c -wp wp_usage/reads.i -wp-timeout 1 -wp-prover alt-ergo,CVC4,Z3 | grep "No prover" )#g' | \
sed 's|@GUI_ALPINE_DEPS@|libart-lgpl-dev|g'| \
sed 's|@GUI_OPAM_DEPS@|cairo2.0.6.1 lablgtk conf-gnomecanvas conf-gtksourceview|g'| \
sed 's|@GUI_REMAKE@|make clean \&\& ./configure --enable-gui \&\& make -j \&\& sudo make install|g' | \
sed 's|@FRAMAC_TESTS@|cd /frama-c \&\& make tests \|\| true|g' | \
sed 's|@OCAMLV@|4.02|g' | \
cat > $@

11.0-stripped: Dockerfile.11.0
	docker build . -t framac/frama-c:$@ --target frama-c-stripped -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-Sodium-20150201.tar.gz $(ARGS)
TARGETS += 11.0-stripped

Dockerfile.11.0: Makefile Dockerfile.template env.template
	sed 's|@ALPINE_OPAM_BASE@|ocaml/opam:alpine-3.12-ocaml-4.02|g' Dockerfile.template | \
sed 's|@ALPINE_BASE@|alpine:3.12|g' | \
sed 's|@CVC4@|$(shell cat cvc4.template)|g' | \
sed 's|@CVC4_VERSION@|1.5|g' | \
sed 's|@Z3@|$(shell cat z3.template)|g' | \
sed 's|@ENV@|$(shell cat env.template)|g' | \
sed 's|@OPAM_CACHE_FIX@|git -C /home/opam/opam-repository pull origin master \&\& |g' | \
sed 's|@OPAM_SWITCH@|true|g' | \
sed 's|@OPAM_DEPS@|\\\
alt-ergo.1.30 \\\
conf-graphviz.0.1 \\\
ocamlfind.1.8.0 \\\
ocamlgraph.1.8.8 \\\
why3.0.88.3 \\\
zarith.1.7 \\\
conf-time.1|' | \
sed 's|@PATCH_FRAMAC@|true|g' | \
sed 's|@WP_REPORT@|-wp -report|g'| \
sed 's|@WHY3_CONFIG@|why3 config --detect-provers|g' | \
sed 's#@WP_TEST@# ! ( printf "int g;\\n//@assigns g;\\nvoid f(){g = 1;}\\nint main() {f(); return g;}" > /tmp/simple.c; frama-c -wp /tmp/simple.c -wp-prover alt-ergo,CVC4,Z3 | grep "No prover" ); rm -f /tmp/simple.c#g' | \
sed 's|@GUI_ALPINE_DEPS@|libart-lgpl-dev|g'| \
sed 's|@GUI_OPAM_DEPS@|cairo2.0.6.1 lablgtk conf-gnomecanvas conf-gtksourceview|g'| \
sed 's|@GUI_REMAKE@|make clean \&\& ./configure --enable-gui \&\& make -j \&\& sudo make install|g' | \
sed 's|@FRAMAC_TESTS@|cd /frama-c \&\& make tests \|\| true|g' | \
sed 's|@OCAMLV@|4.02|g' | \
cat > $@

10.1-stripped: Dockerfile.10.1
	docker build . -t framac/frama-c:$@ --target frama-c-stripped -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-Neon-20140301.tar.gz $(ARGS)
TARGETS += 10.1-stripped

# Starting from this version, due to the usage of a recent GCC, we need to
# remove the `-no-pic` flag that was passed when compiling buckx_c.c.
# Otherwise, we get the dreaded "relocation error".
Dockerfile.10.1: Makefile Dockerfile.template env.template
	sed 's|@ALPINE_OPAM_BASE@|ocaml/opam:alpine-3.12-ocaml-4.02|g' Dockerfile.template | \
sed 's|@ALPINE_BASE@|alpine:3.12|g' | \
sed 's|@CVC4@|$(shell cat cvc4.template)|g' | \
sed 's|@CVC4_VERSION@|1.5|g' | \
sed 's|@Z3@|$(shell cat z3.template)|g' | \
sed 's|@ENV@|$(shell cat env.template)|g' | \
sed 's|@OPAM_CACHE_FIX@|git -C /home/opam/opam-repository pull origin master \&\& |g' | \
sed 's|@OPAM_SWITCH@|true|g' | \
sed 's|@OPAM_DEPS@|\\\
alt-ergo.1.30 \\\
conf-graphviz.0.1 \\\
ocamlfind.1.8.0 \\\
why3-base.0.88.3 \\\
zarith.1.7 \\\
conf-time.1|' | \
sed 's|@PATCH_FRAMAC@|cd /frama-c \&\& sed -i s/-fno-pic// Makefile|g' | \
sed 's|@WP_REPORT@|-wp -report|g'| \
sed 's|@WHY3_CONFIG@|why3 config --detect-provers|g' | \
sed 's#@WP_TEST@# ! ( printf "int g;\\n//@assigns g;\\nvoid f(){g = 1;}\\nint main() {f(); return g;}" > /tmp/simple.c; frama-c -wp /tmp/simple.c -wp-prover alt-ergo,CVC4,Z3 | grep "No prover" ); rm -f /tmp/simple.c#g' | \
sed 's|@GUI_ALPINE_DEPS@|libart-lgpl-dev|g'| \
sed 's|@GUI_OPAM_DEPS@|cairo2.0.6.1 lablgtk conf-gnomecanvas conf-gtksourceview|g'| \
sed 's|@GUI_REMAKE@|make clean \&\& ./configure --enable-gui \&\& make -j \&\& sudo make install|g' | \
sed 's|@FRAMAC_TESTS@|cd /frama-c \&\& make tests \|\| true|g' | \
sed 's|@OCAMLV@|4.02|g' | \
	cat > $@

10.0-stripped: Dockerfile.10.0
	docker build . -t framac/frama-c:$@ --target frama-c-stripped -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-Neon-20140301.tar.gz $(ARGS)
TARGETS += 10.0-stripped

# Starting from this version, due to the usage of a recent GCC, we need to
# remove the `-no-pic` flag that was passed when compiling buckx_c.c.
# Otherwise, we get the dreaded "relocation error".
Dockerfile.10.0: Makefile Dockerfile.template env.template
	sed 's|@ALPINE_OPAM_BASE@|ocaml/opam:alpine-3.12-ocaml-4.02|g' Dockerfile.template | \
sed 's|@ALPINE_BASE@|alpine:3.12|g' | \
sed 's|@CVC4@|$(shell cat cvc4.template)|g' | \
sed 's|@CVC4_VERSION@|1.5|g' | \
sed 's|@Z3@|$(shell cat z3.template)|g' | \
sed 's|@ENV@|$(shell cat env.template)|g' | \
sed 's|@OPAM_CACHE_FIX@|git -C /home/opam/opam-repository pull origin master \&\& |g' | \
sed 's|@OPAM_SWITCH@|true|g' | \
sed 's|@OPAM_DEPS@|\\\
alt-ergo.1.30 \\\
conf-graphviz.0.1 \\\
ocamlfind.1.8.0 \\\
why3-base.0.88.3 \\\
zarith.1.7 \\\
conf-time.1|' | \
sed 's|@PATCH_FRAMAC@|cd /frama-c \&\& sed -i s/-fno-pic// Makefile|g' | \
sed 's|@WP_REPORT@|-wp -report|g'| \
sed 's|@WHY3_CONFIG@|why3 config --detect-provers|g' | \
sed 's#@WP_TEST@# ! ( printf "int g;\\n//@assigns g;\\nvoid f(){g = 1;}\\nint main() {f(); return g;}" > /tmp/simple.c; frama-c -wp /tmp/simple.c -wp-prover alt-ergo,CVC4,Z3 | grep "No prover" ); rm -f /tmp/simple.c#g' | \
sed 's|@GUI_ALPINE_DEPS@|libart-lgpl-dev|g'| \
sed 's|@GUI_OPAM_DEPS@|cairo2.0.6.1 lablgtk conf-gnomecanvas conf-gtksourceview|g'| \
sed 's|@GUI_REMAKE@|make clean \&\& ./configure --enable-gui \&\& make -j \&\& sudo make install|g' | \
sed 's|@FRAMAC_TESTS@|cd /frama-c \&\& make tests \|\| true|g' | \
sed 's|@OCAMLV@|4.02|g' | \
cat > $@

9.2-stripped: Dockerfile.9.2
	docker build . -t framac/frama-c:$@ --target frama-c-stripped -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-Fluorine-20130601.tar.gz $(ARGS)
TARGETS += 9.2-stripped

# configure.in had a bug detecting Make versions > 4; instead of applying
# the proper fix (which would be long), we simply "cheat" by replacing '81'
# (from "make 3.81") with "1".
Dockerfile.9.2: Makefile Dockerfile.template env.template
	sed 's|@ALPINE_OPAM_BASE@|ocaml/opam:alpine-3.12-ocaml-4.02|g' Dockerfile.template | \
sed 's|@ALPINE_BASE@|alpine:3.12|g' | \
sed 's|@CVC4@|$(shell cat cvc4.template)|g' | \
sed 's|@CVC4_VERSION@|1.5|g' | \
sed 's|@Z3@|$(shell cat z3.template)|g' | \
sed 's|@ENV@|$(shell cat env.template)|g' | \
sed 's|@OPAM_CACHE_FIX@|git -C /home/opam/opam-repository pull origin master \&\& |g' | \
sed 's|@OPAM_SWITCH@|opam switch create 3.12.1|g' | \
sed 's|@OPAM_DEPS@|\\\
alt-ergo.1.01 \\\
conf-autoconf.0.1 \\\
conf-graphviz.0.1 \\\
ocamlfind.1.7.3-1 \\\
why3-base.0.85 \\\
zarith.1.7|' | \
sed 's|@PATCH_FRAMAC@|cd /frama-c \&\& sed -i s/-fno-pic// Makefile \&\& sed -i "s/ 81/  1/" configure.in|g' | \
sed 's|@WP_REPORT@|-wp -report|g'| \
sed 's|@WHY3_CONFIG@|why3 config --detect-provers|g' | \
sed 's#@WP_TEST@# ! ( printf "int g;\\n//@assigns g;\\nvoid f(){g = 1;}\\nint main() {f(); return g;}" > /tmp/simple.c; frama-c -wp /tmp/simple.c -wp-prover alt-ergo,CVC4,Z3 | grep "No prover" ); rm -f /tmp/simple.c#g' | \
sed 's|@GUI_ALPINE_DEPS@|libart-lgpl-dev|g'| \
sed 's|@GUI_OPAM_DEPS@|lablgtk conf-gnomecanvas conf-gtksourceview|g'| \
sed 's|@GUI_REMAKE@|make clean \&\& ./configure --enable-gui \&\& make -j \&\& sudo make install|g' | \
sed 's|@FRAMAC_TESTS@|cd /frama-c \&\& make tests \|\| true|g' | \
sed 's|@OCAMLV@|3.12.1|g' | \
cat > $@

8.0-stripped: Dockerfile.8.0
	docker build . -t framac/frama-c:$@ --target frama-c-stripped -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-Oxygen-20120901.tar.gz $(ARGS)
TARGETS += 8.0-stripped

Dockerfile.8.0: Makefile Dockerfile.template env.template
	sed 's|@ALPINE_OPAM_BASE@|ocaml/opam:alpine-3.12-ocaml-4.02|g' Dockerfile.template | \
sed 's|@ALPINE_BASE@|alpine:3.12|g' | \
sed 's|@CVC4@|$(shell cat cvc4.template)|g' | \
sed 's|@CVC4_VERSION@|1.5|g' | \
sed 's|@Z3@|$(shell cat z3.template)|g' | \
sed 's|@ENV@|$(shell cat env.template)|g' | \
sed 's|@OPAM_CACHE_FIX@|git -C /home/opam/opam-repository pull origin master \&\& |g' | \
sed 's|@OPAM_SWITCH@|opam switch create 3.12.1|g' | \
sed 's|@OPAM_DEPS@|\\\
alt-ergo.1.01 \\\
conf-autoconf.0.1 \\\
conf-graphviz.0.1 \\\
ocamlfind.1.7.3-1 \\\
why3-base.0.85 \\\
zarith.1.7|' | \
sed 's|@PATCH_FRAMAC@|cd /frama-c \&\& sed -i s/-fno-pic// Makefile \&\& sed -i "s/ 81/  1/" configure.in|g' | \
sed 's|@WP_REPORT@|-wp -report|g'| \
sed 's|@WHY3_CONFIG@|why3 config --detect-provers|g' | \
sed 's#@WP_TEST@# ! ( printf "int g;\\n//@assigns g;\\nvoid f(){g = 1;}\\nint main() {f(); return g;}" > /tmp/simple.c; frama-c -wp /tmp/simple.c -wp-prover alt-ergo,CVC4,Z3 | grep "No prover" ); rm -f /tmp/simple.c#g' | \
sed 's|@GUI_ALPINE_DEPS@|libart-lgpl-dev|g'| \
sed 's|@GUI_OPAM_DEPS@|lablgtk conf-gnomecanvas conf-gtksourceview|g'| \
sed 's|@GUI_REMAKE@|make clean \&\& ./configure --enable-gui \&\& make -j \&\& sudo make install|g' | \
sed 's|@FRAMAC_TESTS@|cd /frama-c \&\& make tests \|\| true|g' | \
sed 's|@OCAMLV@|3.12.1|g' | \
cat > $@

7.0-stripped: Dockerfile.7.0
	docker build . -t framac/frama-c:$@ --target frama-c-stripped -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-Nitrogen-20111001.tar.gz $(ARGS)
TARGETS += 7.0-stripped

# For some reason, lablgtk2 files are installed in a directory other than the
# one where Frama-C's configure expects them; the simplest fix seems to be
# moving the files to the expected directory.
Dockerfile.7.0: Makefile Dockerfile.template env.template
	sed 's|@ALPINE_OPAM_BASE@|ocaml/opam:alpine-3.12-ocaml-4.02|g' Dockerfile.template | \
sed 's|@ALPINE_BASE@|alpine:3.12|g' | \
sed 's|@CVC4@|$(shell cat cvc4.template)|g' | \
sed 's|@CVC4_VERSION@|1.5|g' | \
sed 's|@Z3@|$(shell cat z3.template)|g' | \
sed 's|@ENV@|$(shell cat env.template)|g' | \
sed 's|@OPAM_CACHE_FIX@|git -C /home/opam/opam-repository pull origin master \&\& |g' | \
sed 's|@OPAM_SWITCH@|opam switch create 3.12.1|g' | \
sed 's|@OPAM_DEPS@|\\\
alt-ergo.1.01 \\\
conf-autoconf.0.1 \\\
conf-graphviz.0.1 \\\
ocamlfind.1.7.3-1 \\\
why3-base.0.85 \\\
zarith.1.7|' | \
sed 's|@PATCH_FRAMAC@|cd /frama-c \&\& sed -i s/-fno-pic// Makefile \&\& sed -i "s/ 81/  1/" configure.in|g' | \
sed 's|@WP_REPORT@|-wp -report|g'| \
sed 's|@WHY3_CONFIG@|why3 config --detect-provers|g' | \
sed 's#@WP_TEST@# ! ( printf "int g;\\n//@assigns g;\\nvoid f(){g = 1;}\\nint main() {f(); return g;}" > /tmp/simple.c; frama-c -wp /tmp/simple.c -wp-prover alt-ergo,CVC4,Z3 | grep "No prover" ); rm -f /tmp/simple.c#g' | \
sed 's|@GUI_ALPINE_DEPS@|libart-lgpl-dev|g'| \
sed 's|@GUI_OPAM_DEPS@|lablgtk conf-gnomecanvas conf-gtksourceview \&\& mv /home/opam/.opam/3.12.1/lib/lablgtk2/ /home/opam/.opam/3.12.1/lib/ocaml/|g'| \
sed 's|@GUI_REMAKE@|make clean \&\& ./configure --enable-gui \&\& make -j \&\& sudo make install|g' | \
sed 's|@FRAMAC_TESTS@|cd /frama-c \&\& make tests \|\| true|g' | \
sed 's|@OCAMLV@|3.12.1|g' | \
cat > $@

6.0-stripped: Dockerfile.6.0
	docker build . -t framac/frama-c:$@ --target frama-c-stripped -f $^ \
--build-arg=from_archive=https://www.frama-c.com/download/frama-c-Carbon-20110201.tar.gz $(ARGS)
TARGETS += 6.0-stripped

# TODO: find out how to make WP installation work; following the instructions, the
# dynamic version fails during ./configure, with:
# ./configure: export: line 1666: ENABLE_USAGE:_FRAMA_C_[OPTIONS_AND_FILES...]: bad variable name
# And the static version (putting in src/wp) fails with:
# src/wp/Makefile:46: *** recipe commences before first target.  Stop.
Dockerfile.6.0: Makefile Dockerfile.template env.template
	sed 's|@ALPINE_OPAM_BASE@|ocaml/opam:alpine-3.12-ocaml-4.02|g' Dockerfile.template | \
sed 's|@ALPINE_BASE@|alpine:3.12|g' | \
sed 's|@ENV@|$(shell cat env.template)|g' | \
sed 's|@CVC4@||g' | \
sed 's|@CVC4_VERSION@||g' | \
sed 's|@Z3@||g' | \
sed 's|@OPAM_CACHE_FIX@|git -C /home/opam/opam-repository pull origin master \&\& |g' | \
sed 's|@OPAM_SWITCH@|opam switch create 3.12.1|g' | \
sed 's|@OPAM_DEPS@|\\\
conf-autoconf.0.1 \\\
conf-graphviz.0.1 \\\
ocamlfind.1.7.3-1|' | \
sed 's|@PATCH_FRAMAC@|cd /frama-c \&\& sed -i s/-fno-pic// Makefile \&\& sed -i "s/ 81/  1/" configure.in|g' | \
sed 's|@WP_REPORT@||g'| \
sed 's|@WHY3_CONFIG@|true|g' | \
sed 's#@WP_TEST@#true#g' | \
sed 's|@GUI_ALPINE_DEPS@|libart-lgpl-dev|g'| \
sed 's|@GUI_OPAM_DEPS@|lablgtk conf-gnomecanvas conf-gtksourceview \&\& mv /home/opam/.opam/3.12.1/lib/lablgtk2/ /home/opam/.opam/3.12.1/lib/ocaml/|g'| \
sed 's|@GUI_REMAKE@|make clean \&\& autoconf \&\& ./configure --enable-gui \&\& make -j \&\& sudo make install|g' | \
sed 's|@FRAMAC_TESTS@|cd /frama-c \&\& make tests \|\| true|g' | \
sed 's|@OCAMLV@|3.12.1|g' | \
cat > $@

#5.0-stripped: Dockerfile.5.0
#	docker build . -t framac/frama-c:$@ --target frama-c-stripped -f $^ \
#--build-arg=from_archive=https://www.frama-c.com/download/frama-c-Boron-20100401-why-2.24.tar.gz $(ARGS)
#TARGETS += 5.0-stripped
#
# Re-running the makefile for the GUI seems to cause issues,
# so we restart everything from the archive
# TODO: fix build and proceed with older Frama-C versions
# Dockerfile.5.0: Makefile Dockerfile.template env.template
# 	sed 's|@ALPINE_OPAM_BASE@|ocaml/opam:alpine-3.12-ocaml-4.02|g' Dockerfile.template | \
# sed 's|@ALPINE_BASE@|alpine:3.12|g' | \
# sed 's|@ENV@|$(shell cat env.template)|g' | \
# sed 's|@CVC4@||g' | \
# sed 's|@CVC4_VERSION@||g' | \
# sed 's|@Z3@||g' | \
# sed 's|@OPAM_CACHE_FIX@|git -C /home/opam/opam-repository pull origin master \&\& |g' | \
# sed 's|@OPAM_SWITCH@|opam switch create 3.12.1|g' | \
# sed 's|@OPAM_DEPS@|\\\
# conf-autoconf.0.1 \\\
# conf-graphviz.0.1 \\\
# ocamlfind.1.7.3-1 \\\
# zarith.1.7|' | \
# sed 's|@PATCH_FRAMAC@|cd /frama-c \&\& sed -i s/-fno-pic// Makefile \&\& sed -i "s/ 81/  1/" configure.in|g' | \
# sed 's|@WP_REPORT@||g'| \
# sed 's|@WHY3_CONFIG@|why3 config --detect-provers|g' | \
# sed 's#@WP_TEST@#true#g' | \
# sed 's|@GUI_ALPINE_DEPS@|libart-lgpl-dev|g'| \
# sed 's|@GUI_OPAM_DEPS@|lablgtk conf-gnomecanvas conf-gtksourceview \&\& mv /home/opam/.opam/3.12.1/lib/lablgtk2/ /home/opam/.opam/3.12.1/lib/ocaml/|g'| \
# sed 's|@GUI_REMAKE@|rm -rf * \&\& wget https://www.frama-c.com/download/frama-c-Boron-20100401-why-2.24.tar.gz \&\& tar xvf frama-c-Boron-20100401-why-2.24.tar.gz --strip 1 \&\& cd /frama-c \&\& sed -i s/-fno-pic// Makefile \&\& sed -i "s/ 81/  1/" configure.in \&\& autoconf \&\& ./configure --enable-gui \&\& make -j \&\& sudo make install|g' | \
# sed 's|@FRAMAC_TESTS@|cd /frama-c \&\& make tests \|\| true|g' | \
# sed 's|@OCAMLV@|3.12.1|g' | \
# cat > $@
