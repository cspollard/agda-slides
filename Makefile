# Agda's GC is ~30% of a clean check; a 1 GB allocation area cuts the user time of
# a clean check of the Pairs modules by about 12% (see plan/Plan.md item 9) for about
# 0.5 GB more peak memory.  Override (`make check AGDA_RTS=`) to use the defaults.
AGDA_RTS ?= +RTS -A1g -RTS
AGDA ?= agda $(AGDA_RTS)

.PHONY: check clean

# Typecheck every module under src/ in a single Agda process (interfaces of
# the libraries are loaded once).  Executables (`*Main`, the spike) import IO
# and need `--guardedness`, so they are checked on their own.
check:
	@mkdir -p _build
	@(echo "module Everything where"; for f in $$(find src -name '*.agda' ! -name '*Main.agda' ! -name Driver.agda ! -path '*/Spike/*' | sort); do \
	    echo "import $$(echo $${f#src/} | sed 's#/#.#g; s#\.agda$$##')"; done) > _build/Everything.agda
	$(AGDA) -i _build _build/Everything.agda
	@for f in $$(find src -name '*Main.agda' -o -name Driver.agda -o -path '*/Spike/*.agda'); do $(AGDA) $$f || exit 1; done

# All executables share one compile directory: MAlonzo output is per module,
# so the (large) library part is translated and compiled by GHC once.
# GHCFLAGS=-O1 for optimised builds.
GHCFLAGS ?= -O0
BUILD_DIR = _build/ghc
COMPILE = $(AGDA) --compile --compile-dir=$(BUILD_DIR) --ghc-flag=$(GHCFLAGS)

clean:
	find . -name '*.agdai' -delete
	rm -rf MAlonzo _build out

# R0 spike: write out/spike/{index.html,init.js}.  REVEAL points at an
# unpacked reveal.js distribution (e.g. `npm install reveal.js`).
REVEAL ?= $(CURDIR)/node_modules/reveal.js

.PHONY: spike
spike:
	mkdir -p out/spike $(BUILD_DIR)
	ln -sfn $(REVEAL) out/spike/reveal
	$(COMPILE) src/Slides/Spike/Reveal.agda
	mv Reveal $(BUILD_DIR)/Reveal 2>/dev/null || true
	$(BUILD_DIR)/Reveal
	cp assets/slides.css assets/animation.js out/spike/

# Render any deck: `make deck MAIN=src/MyTalkMain.agda NAME=mytalk`, where the
# main module writes to out/$(NAME).  Puts reveal.js and the stylesheet next to
# the output and runs the compiled program.
NAME ?= mytalk
.PHONY: deck
deck:
	mkdir -p out/$(NAME) $(BUILD_DIR)
	ln -sfn $(REVEAL) out/$(NAME)/reveal
	cp assets/slides.css assets/animation.js assets/plot.svg out/$(NAME)/
	$(COMPILE) $(MAIN)
	mv $(basename $(notdir $(MAIN))) $(BUILD_DIR)/ 2>/dev/null || true
	$(BUILD_DIR)/$(basename $(notdir $(MAIN)))

# Render the example deck to out/intro/.
.PHONY: example
example:
	mkdir -p out/intro $(BUILD_DIR)
	ln -sfn $(REVEAL) out/intro/reveal
	cp assets/slides.css assets/animation.js out/intro/
	$(COMPILE) src/Slides/Examples/IntroMain.agda
	mv IntroMain $(BUILD_DIR)/IntroMain 2>/dev/null || true
	$(BUILD_DIR)/IntroMain

# Golden-file tests for the example decks (run `make example talk plain showcase` first).
.PHONY: test test-browser
test:
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
	diff -u tests/golden/pairs.index.html out/pairs/index.html
	diff -u tests/golden/pairs.init.js out/pairs/init.js
	diff -u tests/golden/pairs.css out/pairs/pairs.css
	diff -u tests/golden/plain.js out/plain/plain.js
	diff -u tests/golden/animation.js out/plain/animation.js
	diff -u tests/golden/plain.css out/plain/plain.css

# Load the rendered deck in headless Chrome (set CHROME to override the binary).
test-browser:
	python3 tests/check_reveal.py out/intro/index.html
	python3 tests/check_reveal.py out/talk/index.html
	python3 tests/check_plain.py out/plain/index.html
	python3 tests/check_reveal.py out/showcase/index.html
	python3 tests/check_plain.py out/showcase-plain/index.html
	python3 tests/check_plain.py out/showcase-lowered/index.html
	python3 tests/check_plain.py out/showcase-still/index.html

# Render the component-based example deck to out/talk/.
.PHONY: talk
talk:
	mkdir -p out/talk $(BUILD_DIR)
	ln -sfn $(REVEAL) out/talk/reveal
	cp assets/slides.css assets/animation.js assets/plot.svg out/talk/
	$(COMPILE) src/Slides/Examples/TalkMain.agda
	mv TalkMain $(BUILD_DIR)/TalkMain 2>/dev/null || true
	$(BUILD_DIR)/TalkMain

# Render the component-based deck as standalone HTML to out/plain/.
.PHONY: plain
plain:
	mkdir -p out/plain $(BUILD_DIR)
	cp assets/plain.css assets/plain.js assets/animation.js assets/slides.css assets/plot.svg out/plain/
	$(COMPILE) src/Slides/Examples/PlainMain.agda
	mv PlainMain $(BUILD_DIR)/PlainMain 2>/dev/null || true
	$(BUILD_DIR)/PlainMain

# Decks that refer to a resource they did not declare must not typecheck.
.PHONY: test-negative check-resources
test-negative:
	@for f in tests/negative/*.agda; do \
	  if out=$$($(AGDA) -i tests/negative $$f 2>&1); then \
	    echo "FAIL $$f typechecks but should not"; exit 1; \
	  elif echo "$$out" | grep -q "No instance of type"; then echo "ok   $$f is rejected"; \
	  else echo "FAIL $$f failed for another reason:"; echo "$$out"; exit 1; fi; \
	done

# Declared figures exist next to the rendered decks (run `make talk plain` first).
check-resources:
	python3 tests/check_resources.py src/Slides/Examples/Talk.agda out/talk
	python3 tests/check_resources.py src/Slides/Examples/Talk.agda out/plain

# Render the showcase deck with both backends to out/showcase/ and out/showcase-plain/,
# and lowered (no notes, no diagrams) to out/showcase-lowered/, and (no notes, animations
# as stills) to out/showcase-still/.
.PHONY: showcase
showcase:
	mkdir -p out/showcase out/showcase-plain out/showcase-lowered out/showcase-still $(BUILD_DIR)
	ln -sfn $(REVEAL) out/showcase/reveal
	cp assets/slides.css assets/animation.js assets/plot.svg out/showcase/
	cp assets/plain.css assets/plain.js assets/animation.js assets/slides.css assets/plot.svg out/showcase-plain/
	cp assets/plain.css assets/plain.js assets/animation.js assets/slides.css assets/plot.svg out/showcase-lowered/
	cp assets/plain.css assets/plain.js assets/animation.js assets/slides.css assets/plot.svg out/showcase-still/
	$(COMPILE) src/Slides/Examples/ShowcaseMain.agda
	mv ShowcaseMain $(BUILD_DIR)/ShowcaseMain 2>/dev/null || true
	$(BUILD_DIR)/ShowcaseMain

# The "It Just Takes Two" deck (docs/PairsDeck.md).  `make pairs` loads reveal.js and
# KaTeX from a CDN (out/pairs/, needs network in the browser); `make pairs-local
# REVEAL=…` links a local copy of reveal.js (out/pairs-local/).
PAIRS_FILES = assets/slides.css assets/animation.js assets/pairs/pairs.css

.PHONY: pairs pairs-local
pairs:
	mkdir -p out/pairs $(BUILD_DIR)
	cp $(PAIRS_FILES) out/pairs/
	$(COMPILE) src/Slides/Examples/PairsMain.agda
	mv PairsMain $(BUILD_DIR)/PairsMain 2>/dev/null || true
	$(BUILD_DIR)/PairsMain cdn

pairs-local:
	mkdir -p out/pairs-local $(BUILD_DIR)
	ln -sfn $(REVEAL) out/pairs-local/reveal
	cp $(PAIRS_FILES) out/pairs-local/
	$(COMPILE) src/Slides/Examples/PairsMain.agda
	mv PairsMain $(BUILD_DIR)/PairsMain 2>/dev/null || true
	$(BUILD_DIR)/PairsMain local

# Drive the rendered showcase deck in a real browser (keyboard, fragments, config).
# Needs `make showcase` first and `npm install` in tests/browser once.
.PHONY: test-playwright
test-playwright:
	cd tests/browser && npm install --silent
	node tests/browser/run.mjs out

# Step through the animation slide of the intro deck (needs `make example` and a
# reveal.js copy linked at out/intro/reveal).
.PHONY: test-anim
test-anim:
	cd tests/browser && npm install --silent
	node tests/browser/anim.mjs out

# Play the animations of the standalone backend (needs `make showcase`).
.PHONY: test-plain-anim
test-plain-anim:
	cd tests/browser && npm install --silent
	node tests/browser/plain-anim.mjs out

# The page player against the frames Agda computes (`animref` renders a deck of
# animations and their reference frames, standalone, to out/animref/).
.PHONY: animref test-anim-ref
animref:
	mkdir -p out/animref $(BUILD_DIR)
	cp assets/plain.css assets/plain.js assets/animation.js assets/slides.css out/animref/
	$(COMPILE) src/Slides/Examples/AnimRefMain.agda
	mv AnimRefMain $(BUILD_DIR)/AnimRefMain 2>/dev/null || true
	$(BUILD_DIR)/AnimRefMain

test-anim-ref: animref
	cd tests/browser && npm install --silent
	node tests/browser/anim-ref.mjs out

# Drive the "It Just Takes Two" deck (needs `make pairs` first; also drives the
# local-copy build if `make pairs-local` has been run).
.PHONY: test-pairs
test-pairs:
	cd tests/browser && npm install --silent
	node tests/browser/pairs.mjs out pairs
	@if [ -d out/pairs-local ]; then node tests/browser/pairs.mjs out pairs-local; fi
