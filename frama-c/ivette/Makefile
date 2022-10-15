##########################################################################
#                                                                        #
#  This file is part of Frama-C.                                         #
#                                                                        #
#  Copyright (C) 2007-2022                                               #
#    CEA (Commissariat à l'énergie atomique et aux énergies              #
#         alternatives)                                                  #
#                                                                        #
#  you can redistribute it and/or modify it under the terms of the GNU   #
#  Lesser General Public License as published by the Free Software       #
#  Foundation, version 2.1.                                              #
#                                                                        #
#  It is distributed in the hope that it will be useful,                 #
#  but WITHOUT ANY WARRANTY; without even the implied warranty of        #
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         #
#  GNU Lesser General Public License for more details.                   #
#                                                                        #
#  See the GNU Lesser General Public License version 2.1                 #
#  for more details (enclosed in the file licenses/LGPLv2.1).            #
#                                                                        #
##########################################################################

# --------------------------------------------------------------------------
APP=Ivette
DOME=./src/dome
DOME_ARGS=--command $$(dirname $$0)/../../bin/frama-c
DOME_DEV=-server-debug 1
DOME_CLI=./bin/ivette
DOME_API=./src/frama-c
DOME_CUSTOM_ENTRIES= yes
COPYRIGHT=CEA LIST / LSL
# --------------------------------------------------------------------------

.PHONY: all app dev pkg doc serve dist lint fixlint checkcase

all: pkg lint app

app: dome-app
dev: dome-dev
dist: dist-dir dome-dist

lint: dome-pkg dome-templ checkcase
	@echo "[Ivette] running typechecker & linter"
	yarn run typecheck
	yarn run lint

# In case-insensitive filesystems (macOS/Windows), import statements and
# filenames can have issues due to case differences
checkcase:
	@echo "[Ivette] check case issues in imported filenames"
	@err=0 ; for f in `find src | sed -E 's/(.ts|.tsx|.js|.jsx|.css|.json)$$//' | sort -f | uniq -di` ;\
	 do \
		err=1; \
		echo " - ambiguous $$f.*"; \
	 done ;\
	 exit $$err

tsc: dome-pkg dome-templ
	@echo "[Ivette] running typechecker & linter (with cache & fix mode)"
	yarn run typecheck
	yarn run lint --fix --cache --cache-location .eslint-cache

# --------------------------------------------------------------------------
# --- Ivette Package Loader
# --------------------------------------------------------------------------

LOADER=src/renderer/loader.ts
SANDBOX=src/renderer/sandbox.ts
PACKAGES=$(shell find src -name "pkg.json")
SANDBOXES=$(shell find src/sandbox -name "*.tsx")

lint: pkg
dome-pkg: pkg
dome-app: pkg
dome-dev: pkg
dome-dist: pkg

pkg: $(LOADER) $(SANDBOX)

$(LOADER): $(PACKAGES) ./configure.js ./Makefile
	@rm -f $@
	@echo "[Ivette] configure packages"
	@node ./configure.js $@ $(PACKAGES)
	@chmod -f a-w $@

$(SANDBOX): $(SANDBOXES) ./sandboxer.js ./Makefile
	@rm -f $@
	@echo "[Ivette] configure sandboxes"
	@node ./sandboxer.js $@ $(SANDBOXES)
	@chmod -f a-w $@

# --------------------------------------------------------------------------
# --- Frama-C Source Distrib
# --------------------------------------------------------------------------

.PHONY: update-distrib-files

update-distrib-files:
	./distrib.sh

# --------------------------------------------------------------------------
# --- Frama-C API
# --------------------------------------------------------------------------

.PHONY: api

api:
	@echo "[Ivette] Generating TypeScript API"
	@find src/frama-c -path "*/api/*" -name "*.ts" -exec rm -f {} \;
	../bin/frama-c.byte \
		-load-module src/frama-c/api_generator.ml \
		-server-tsc
	@find src/frama-c -path "*/api/*" -name "*.ts" \
		-exec headache \
			-h ../headers/open-source/CEA_LGPL \
			-c ../headers/headache_config.txt {} \;\
		-exec chmod a-w {} \;

# --------------------------------------------------------------------------
# --- Ivette Documentation
# --------------------------------------------------------------------------

.PHONY: icons

VERSION=$(shell echo "console.log(require('./package.json').version)" | node -)

DOC_ICONS_CSS= src/dome/doc/gallery.css
DOC_ICONS_MAKE= src/dome/doc/iconsmd.js
DOC_ICONS_GALLERY= src/dome/doc/guides/icons.md
DOC_ICONS_DATA= src/dome/renderer/controls/gallery.json
DOC_GUIDES= src/dome/doc/guides

NODEBIN= ./node_modules/.bin

DOCDIRS= src/ivette src/dome/renderer src/dome/utils src/frama-c/api
DOCFILES= src/frama-c/server.ts src/frama-c/states.ts $(shell find $(DOCDIRS) -name "*.ts" -or -name "*.tsx")

icons: $(DOC_ICONS_GALLERY)

$(DOC_ICONS_GALLERY): $(DOC_ICONS_MAKE) $(DOC_ICONS_DATA)
	@rm -f $@
	@node $(DOC_ICONS_MAKE) $(DOC_ICONS_DATA) > src/dome/doc/guides/icons.md
	@chmod a-w $@

doc: $(NODEBIN)/typedoc icons
	@echo "\n[Ivette] documentation"
	@rm -fr doc/html
	@yarn run typedoc $(DOCFILES)
	@echo "\n[Ivette] main page"
	@echo ""
	@echo "   file://$(PWD)/ivette/doc/html/index.html"
	@echo ""

$(NODEBIN)/%:
	@echo "[Node] install package $*"
	yarn add -D $*

# --------------------------------------------------------------------------
include $(DOME)/template/makefile
# --------------------------------------------------------------------------

# --------------------------------------------------------------------------
# --- Ivette Installation
# --------------------------------------------------------------------------

sinclude ../share/Makefile.config

dist-dir:
	@echo "Cleaning dist"
	@rm -fr dist

IVETTE_DIST=$(wildcard dist/linux-unpacked dist/mac dist/mac-arm64)

ifdef LIBDIR
ifdef BINDIR
ifeq ($(IVETTE_DIST),dist/linux-unpacked)

install:
	@echo "Installing Ivette (Linux)"
	@rm -fr $(LIBDIR)/ivette
	@rm -f $(BINDIR)/ivette
	@mv $(IVETTE_DIST) $(LIBDIR)/ivette
	@ln -s $(LIBDIR)/ivette/ivette $(BINDIR)/ivette

else ifeq ($(IVETTE_DIST:-arm64=),dist/mac)

install:
	@echo "Installing Ivette (macOS)"
	@rm -fr /Applications/Ivette.app
	@mv $(IVETTE_DIST)/Ivette.app /Applications/
	@rm -fr $(IVETTE_DIST)
	@install ivette-macos.sh $(BINDIR)/ivette

else

install:
	@echo "No distribution to install"
	@echo "use 'make dist' and retry"
	@exit 1

endif
endif
endif

# --------------------------------------------------------------------------
# --- Ivette Un-Installation
# --------------------------------------------------------------------------

ifdef LIBDIR
ifdef BINDIR

uninstall:
	@echo "Uninstall Ivette"
	@rm -fr dist
	@rm -fr /Applications/Ivette.app
	@rm -fr $(LIBDIR)/ivette
	@rm -f $(BINDIR)/ivette

endif
endif

# --------------------------------------------------------------------------
