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
	@(echo "module Everything where"; for f in $$(find src \( -name '*.agda' -o -name '*.lagda.md' \) ! -name '*Main.agda' ! -name Driver.agda | sort); do \
	    echo "import $$(echo $${f#src/} | sed -E 's#/#.#g; s#\.(agda|lagda\.md)$$##')"; done) > _build/Everything.agda
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
KATEX  ?= $(CURDIR)/node_modules/katex
FIRA   ?= $(CURDIR)/node_modules/@fontsource/fira-code

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

# The "It Just Takes Two" deck.  `make pairs` loads reveal.js and KaTeX from a CDN (out/pairs/,
# needs network in the browser); `make pairs-local REVEAL=...` links a local copy of reveal.js
# (out/pairs-local/).
PAIRS_FILES = assets/slides.css assets/animation.js assets/light.css assets/pairs/pairs.css

.PHONY: pairs pairs-local test-pairs
pairs:
	mkdir -p out/pairs $(BUILD_DIR)
	cp $(PAIRS_FILES) out/pairs/
	$(call run-main,src/Slides/Examples/PairsMain.agda,cdn)

pairs-local:
	mkdir -p out/pairs-local $(BUILD_DIR)
	ln -sfn $(REVEAL) out/pairs-local/reveal
	cp $(PAIRS_FILES) out/pairs-local/
	$(call run-main,src/Slides/Examples/PairsMain.agda,local)

# Drive the deck (needs `make pairs` first; also drives the local-copy build if `make pairs-local`
# has been run).
test-pairs:
	cd tests/browser && npm install --silent
	node tests/browser/pairs.mjs out pairs
	@if [ -d out/pairs-local ]; then node tests/browser/pairs.mjs out pairs-local; fi

# The outreach deck "How collider physics is accelerating data science", a literate Agda file
# (src/Slides/Examples/Collider.lagda.md, the deck in ColliderSlides.lagda.md).  `make collider`
# loads reveal.js and KaTeX from a CDN (out/collider/); `make collider-local REVEAL=... KATEX=...` links a
# local copy of both (out/collider-local/). 
COLLIDER_FILES = assets/slides.css assets/animation.js assets/light.css assets/collider/collider.css assets/collider/CMSID.jpg assets/collider/ATLASMS.jpg assets/collider/LHC-FCC.jpg

.PHONY: collider collider-local
collider:
	mkdir -p out/collider $(BUILD_DIR)
	cp $(COLLIDER_FILES) out/collider/
	$(call run-main,src/Slides/Examples/ColliderMain.agda,cdn)

collider-local:
	mkdir -p out/collider-local $(BUILD_DIR)
	ln -sfn $(REVEAL) out/collider-local/reveal
	ln -sfn $(KATEX) out/collider-local/katex
	cp $(COLLIDER_FILES) out/collider-local/
	mkdir -p out/collider-local/fonts
	for w in 400 600 700; do cp $(FIRA)/files/fira-code-latin-$$w-normal.woff2 out/collider-local/fonts/; \
	  echo "@font-face{font-family:'Fira Code';font-weight:$$w;font-display:swap;src:url(fonts/fira-code-latin-$$w-normal.woff2) format('woff2');}"; done > out/collider-local/fira.css
	sed "1s#.*#@import url('fira.css');#" assets/collider/collider.css > out/collider-local/collider.css
	$(call run-main,src/Slides/Examples/ColliderMain.agda,local)

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

# Programs that must not typecheck (tests/negative/*.agda): a resource a deck did not declare,
# animation phases of unequal length, two commands bound to one key, a deck presented on a backend
# that binds none of `Nav`.  Each file says `-- EXPECT: <regex>`, the message of the rejection (the
# unsolved check, or the false equation); tests/negative/controls/*.agda are the valid
# counterparts and MUST typecheck, so a rejection cannot come from a typo.
.PHONY: test-negative
test-negative:
	@for f in tests/negative/*.agda; do \
	  pat=$$(sed -n 's/^-- EXPECT: //p' $$f); \
	  [ -n "$$pat" ] || { echo "FAIL $$f has no EXPECT line"; exit 1; }; \
	  if out=$$($(AGDA) -i tests/negative $$f 2>&1); then \
	    echo "FAIL $$f typechecks but should not"; exit 1; \
	  elif echo "$$out" | grep -q "$$pat"; then echo "ok   $$f is rejected"; \
	  else echo "FAIL $$f failed for another reason:"; echo "$$out"; exit 1; fi; \
	done
	@for f in tests/negative/controls/*.agda; do \
	  $(AGDA) -i tests/negative/controls $$f >/dev/null && echo "ok   $$f typechecks" || { echo "FAIL $$f"; exit 1; }; done

# Golden-file tests (run `make example talk plain showcase` first), then the browser tests.
.PHONY: test test-browser
test:
	python3 tests/check_closure.py
	python3 tests/check_plain_keys.py
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
	diff -u tests/golden/pairs.index.html out/pairs/index.html
	diff -u tests/golden/pairs.init.js out/pairs/init.js
	diff -u tests/golden/pairs.css out/pairs/pairs.css
	diff -u tests/golden/light.css out/pairs/light.css

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

# Declared figures exist next to the rendered decks (run `make talk plain` first).
.PHONY: check-resources
check-resources:
	python3 tests/check_resources.py src/Slides/Examples/Talk.agda out/talk
	python3 tests/check_resources.py src/Slides/Examples/Talk.agda out/plain

# Drive the rendered showcase deck in a real browser (keyboard, fragments, config).
.PHONY: test-playwright test-anim test-plain-anim test-nav test-browser-all
test-playwright:
	cd tests/browser && npm install --silent
	node tests/browser/run.mjs out

# Step through the animation slides of the intro deck (needs `make example`).
test-anim:
	cd tests/browser && npm install --silent
	node tests/browser/anim.mjs out

# Play the animations of the standalone backend (needs `make showcase`).
test-plain-anim:
	cd tests/browser && npm install --silent
	node tests/browser/plain-anim.mjs out

# Pin how decks are navigated (next/prev/first/last/goto/overview, fragments, both backends, and
# that the two backends walk a deck identically).  Needs `make example talk plain showcase`.
test-nav:
	cd tests/browser && npm install --silent
	node tests/browser/nav.mjs out

# Every browser test that needs only local files (test-pairs needs a CDN, or `make pairs-local`).
test-browser-all: test-browser test-playwright test-anim test-plain-anim test-nav test-keys test-labels test-anim-ref
