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

# The showcase deck with both backends: out/showcase/ (reveal.js) and out/showcase-plain/, and
# lowered (no notes, no diagrams) to out/showcase-lowered/, (no notes, animations as stills) to
# out/showcase-still/.
.PHONY: showcase
showcase:
	mkdir -p out/showcase out/showcase-plain out/showcase-lowered out/showcase-still $(BUILD_DIR)
	ln -sfn $(REVEAL) out/showcase/reveal
	cp assets/slides.css assets/animation.js assets/plot.svg out/showcase/
	cp $(PLAIN_FILES) out/showcase-plain/
	cp $(PLAIN_FILES) out/showcase-lowered/
	cp $(PLAIN_FILES) out/showcase-still/
	$(call run-main,src/Slides/Examples/ShowcaseMain.agda)

# A deck with a non-default key binding (not a golden), and a deck with named slides.
.PHONY: keys labels test-keys test-labels
keys:
	mkdir -p out/keys $(BUILD_DIR)
	ln -sfn $(REVEAL) out/keys/reveal
	cp assets/slides.css assets/animation.js out/keys/
	$(call run-main,src/Slides/Examples/KeysMain.agda)

labels:
	mkdir -p out/labels $(BUILD_DIR)
	ln -sfn $(REVEAL) out/labels/reveal
	cp assets/slides.css assets/animation.js out/labels/
	$(call run-main,src/Slides/Examples/LabelsMain.agda)

test-keys: keys
	cd tests/browser && npm install --silent
	node tests/browser/keys.mjs out

test-labels: labels
	cd tests/browser && npm install --silent
	node tests/browser/labels.mjs out

# Golden-file tests (run `make example talk plain showcase` first), then the browser tests.
.PHONY: test test-browser
test:
	python3 tests/check_closure.py
	diff -u tests/golden/intro.index.html out/intro/index.html
	diff -u tests/golden/intro.init.js out/intro/init.js
	diff -u tests/golden/slides.css out/intro/slides.css
	diff -u tests/golden/talk.index.html out/talk/index.html
	diff -u tests/golden/plain.index.html out/plain/index.html
	diff -u tests/golden/showcase.index.html out/showcase/index.html
	diff -u tests/golden/showcase.init.js out/showcase/init.js
	diff -u tests/golden/showcase-plain.index.html out/showcase-plain/index.html
	diff -u tests/golden/showcase-lowered.index.html out/showcase-lowered/index.html
	diff -u tests/golden/showcase-still.index.html out/showcase-still/index.html
	diff -u tests/golden/animation.js out/plain/animation.js
	diff -u tests/golden/plain.js out/plain/plain.js
	diff -u tests/golden/plain.css out/plain/plain.css

test-browser:
	python3 tests/check_reveal.py out/intro/index.html
	python3 tests/check_reveal.py out/talk/index.html
	python3 tests/check_plain.py out/plain/index.html
	python3 tests/check_reveal.py out/showcase/index.html
	python3 tests/check_plain.py out/showcase-plain/index.html
	python3 tests/check_plain.py out/showcase-lowered/index.html
	python3 tests/check_plain.py out/showcase-still/index.html
	node tests/browser/anim.mjs out
	node tests/browser/plain-anim.mjs out

# The page evaluator against the frames Agda computes (`animref` writes a standalone deck of
# animations and `refs.json` to out/animref/).
.PHONY: animref test-anim-ref
animref:
	mkdir -p out/animref $(BUILD_DIR)
	cp assets/plain.css assets/plain.js assets/animation.js assets/slides.css out/animref/
	$(call run-main,src/Slides/Examples/AnimRefMain.agda)

test-anim-ref: animref
	cd tests/browser && npm install --silent
	node tests/browser/anim-ref.mjs out
