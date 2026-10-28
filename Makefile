# Minimal while the library is rebuilt (plan/Rebuild.md).  The legacy Makefile is at
# ../agda-slides-legacy/Makefile; written for BSD tools (sed -E, no `\?`).
AGDA_RTS ?= +RTS -A1g -RTS
AGDA_FLAGS ?=
AGDA ?= agda $(AGDA_RTS) $(AGDA_FLAGS)

.PHONY: check clean

# Typecheck every module under src/ in one Agda process.  Executables (`*Main.agda`,
# `Driver.agda`) need --guardedness and are checked on their own.
check:
	@mkdir -p _build
	@(echo "module Everything where"; for f in $$(find src -name '*.agda' ! -name '*Main.agda' ! -name Driver.agda | sort); do \
	    echo "import $$(echo $${f#src/} | sed -E 's#/#.#g; s#\.agda$$##')"; done) > _build/Everything.agda
	$(AGDA) -i _build _build/Everything.agda
	@for f in $$(find src -name '*Main.agda' -o -name Driver.agda); do $(AGDA) $$f || exit 1; done

.PHONY: html
html:
	@mkdir -p build
	@(echo "{-# OPTIONS --guardedness #-}"; echo "module Everything where"; for f in $$(find src -name '*.agda' | sort); do \
	    echo "import $$(echo $${f#src/} | sed -E 's#/#.#g; s#\.agda$$##')"; done) > build/Everything.agda
	$(AGDA) --html --html-dir=html -i build build/Everything.agda

# All executables share one compile directory: MAlonzo output is per module, so the (large)
# library part is translated and compiled by GHC once.  -O0 and -j are the fastest build.
GHCFLAGS ?= -O0
GHCJOBS ?= -j
BUILD_DIR = _build/ghc
COMPILE = $(AGDA) --compile --compile-dir=$(BUILD_DIR) --ghc-flag=$(GHCFLAGS) --ghc-flag=$(GHCJOBS)

# What the standalone (plain) decks need next to index.html.
PLAIN_FILES = assets/plain.css assets/plain.js assets/animation.js assets/slides.css assets/plot.svg

# Compile the executable module $(1) (the binary lands in the compile directory) and run it
# with the arguments $(2).
define run-main
$(COMPILE) $(1)
$(BUILD_DIR)/$(basename $(notdir $(1))) $(2)
endef

clean:
	find . -name '*.agdai' -delete
	rm -rf MAlonzo _build out build html

# REVEAL points at an unpacked reveal.js distribution (`npm install reveal.js`).
REVEAL ?= $(CURDIR)/node_modules/reveal.js

# Render the example deck to out/intro/.
.PHONY: example talk plain
example:
	mkdir -p out/intro $(BUILD_DIR)
	ln -sfn $(REVEAL) out/intro/reveal
	cp assets/slides.css assets/animation.js out/intro/
	$(call run-main,src/Slides/Examples/IntroMain.agda)

# Render the component-based deck to out/talk/ (reveal.js) and out/plain/ (standalone HTML).
talk:
	mkdir -p out/talk $(BUILD_DIR)
	ln -sfn $(REVEAL) out/talk/reveal
	cp assets/slides.css assets/animation.js assets/plot.svg out/talk/
	$(call run-main,src/Slides/Examples/TalkMain.agda)

plain:
	mkdir -p out/plain $(BUILD_DIR)
	cp $(PLAIN_FILES) out/plain/
	$(call run-main,src/Slides/Examples/PlainMain.agda)
