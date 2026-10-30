# Targets: check/html (typecheck, docs), example..labels (build decks to out/), test-* (see each).
# Written for BSD tools (sed -E, no `\?`).
AGDA_RTS ?= +RTS -A1g -RTS
AGDA_FLAGS ?=
AGDA ?= agda $(AGDA_RTS) $(AGDA_FLAGS)

.PHONY: check clean

# Typecheck src/ in one Agda process; executables (`*Main.agda`, `Driver.agda`) need --guardedness
# and are checked one by one.
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

# All executables share one compile directory, so the library is compiled by GHC once.
GHCFLAGS ?= -O0
GHCJOBS ?= -j
BUILD_DIR = _build/ghc
COMPILE = $(AGDA) --compile --compile-dir=$(BUILD_DIR) --ghc-flag=$(GHCFLAGS) --ghc-flag=$(GHCJOBS)

# What the standalone (plain) decks need next to index.html.
PLAIN_FILES = assets/plain.css assets/plain.js assets/animation.js assets/slides.css assets/plot.svg

# Compile executable module $(1), run it with arguments $(2).
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

# Single-backend decks: Intro (out/intro), TextDemo (out/text), Talk (reveal: out/talk; plain: out/plain).
.PHONY: example talk plain
example:
	mkdir -p out/intro $(BUILD_DIR)
	ln -sfn $(REVEAL) out/intro/reveal
	cp assets/slides.css assets/animation.js out/intro/
	$(call run-main,src/Slides/Examples/IntroMain.agda)

.PHONY: text
text:
	mkdir -p out/text $(BUILD_DIR)
	ln -sfn $(REVEAL) out/text/reveal
	cp assets/slides.css assets/animation.js out/text/
	$(call run-main,src/Slides/Examples/TextDemoMain.agda)

# A 3D cube for a tensor slide (out/tensor; not a golden).
.PHONY: tensor
tensor:
	mkdir -p out/tensor $(BUILD_DIR)
	ln -sfn $(REVEAL) out/tensor/reveal
	cp assets/slides.css assets/animation.js out/tensor/
	$(call run-main,src/Slides/Examples/TensorMain.agda)

talk:
	mkdir -p out/talk $(BUILD_DIR)
	ln -sfn $(REVEAL) out/talk/reveal
	cp assets/slides.css assets/animation.js assets/plot.svg out/talk/
	$(call run-main,src/Slides/Examples/TalkMain.agda)

plain:
	mkdir -p out/plain $(BUILD_DIR)
	cp $(PLAIN_FILES) out/plain/
	$(call run-main,src/Slides/Examples/PlainMain.agda)

# Plots (Slides.Plot): out/plots.
.PHONY: plots
plots:
	mkdir -p out/plots $(BUILD_DIR)
	ln -sfn $(REVEAL) out/plots/reveal
	cp assets/slides.css assets/plots.css assets/animation.js out/plots/
	$(call run-main,src/Slides/Examples/PlotsMain.agda)

# The same look with the data read from `data/spectrum.csv` (out/plot-data).
.PHONY: plot-data
plot-data:
	mkdir -p out/plot-data $(BUILD_DIR)
	ln -sfn $(REVEAL) out/plot-data/reveal
	cp assets/slides.css assets/plots.css assets/animation.js out/plot-data/
	$(call run-main,src/Slides/Examples/PlotsDataMain.agda)

# Showcase on both backends plus the lowered variants (out/showcase*).
.PHONY: showcase
showcase:
	mkdir -p out/showcase out/showcase-plain out/showcase-lowered out/showcase-still $(BUILD_DIR)
	ln -sfn $(REVEAL) out/showcase/reveal
	cp assets/slides.css assets/animation.js assets/plot.svg out/showcase/
	cp $(PLAIN_FILES) out/showcase-plain/
	cp $(PLAIN_FILES) out/showcase-lowered/
	cp $(PLAIN_FILES) out/showcase-still/
	$(call run-main,src/Slides/Examples/ShowcaseMain.agda)

# The Pairs deck: `pairs` loads reveal.js and KaTeX from a CDN (needs network in the browser);
# `pairs-local REVEAL=...` links a local reveal.js.
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

# Drive Pairs in a browser (needs `make pairs`; also `pairs-local` if built).
test-pairs:
	cd tests/browser && npm install --silent
	node tests/browser/pairs.mjs out pairs
	@if [ -d out/pairs-local ]; then node tests/browser/pairs.mjs out pairs-local; fi

# The Collider outreach deck (literate Agda): `collider` uses CDNs, `collider-local` links local
# reveal.js, KaTeX and fonts.
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

# Decks for the key-binding and label-navigation tests (not goldens).
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

# tests/negative/*.agda must be rejected with the message matching their `-- EXPECT: <regex>`;
# tests/negative/controls/*.agda are the valid counterparts and must typecheck.
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

# Numeric checks of Slides.Trig against exact values (slow, so not in `check`).
.PHONY: test-numeric
test-numeric:
	$(AGDA) -i tests/numeric tests/numeric/TrigCheck.agda
	$(AGDA) -i tests/numeric tests/numeric/ThreeCheck.agda

# Golden-file diffs (needs `make example text talk plain showcase pairs`); test-browser: headless-Chrome checks.
.PHONY: test test-browser
test:
	python3 tests/check_closure.py
	python3 tests/check_plain_keys.py
	diff -u tests/golden/intro.index.html out/intro/index.html
	diff -u tests/golden/intro.init.js out/intro/init.js
	diff -u tests/golden/slides.css out/intro/slides.css
	diff -u tests/golden/text.index.html out/text/index.html
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

# The page evaluator against the frames Agda computes (`animref` writes the deck and refs.json).
.PHONY: animref test-anim-ref
animref:
	mkdir -p out/animref $(BUILD_DIR)
	cp assets/plain.css assets/plain.js assets/animation.js assets/slides.css out/animref/
	$(call run-main,src/Slides/Examples/AnimRefMain.agda)

test-anim-ref: animref
	cd tests/browser && npm install --silent
	node tests/browser/anim-ref.mjs out

# Declared figures exist next to the rendered decks (needs `make talk plain`).
.PHONY: check-resources
check-resources:
	python3 tests/check_resources.py src/Slides/Examples/Talk.agda out/talk
	python3 tests/check_resources.py src/Slides/Examples/Talk.agda out/plain

# Playwright tests on rendered decks: test-playwright (showcase: keys, fragments, config), test-anim
# (intro, needs `make example`), test-plain-anim (needs `make showcase`), test-nav (navigation, both
# backends; needs `make example talk plain showcase`).
.PHONY: test-playwright test-anim test-plain-anim test-nav test-browser-all
test-playwright:
	cd tests/browser && npm install --silent
	node tests/browser/run.mjs out

test-anim:
	cd tests/browser && npm install --silent
	node tests/browser/anim.mjs out

test-plain-anim:
	cd tests/browser && npm install --silent
	node tests/browser/plain-anim.mjs out

test-nav:
	cd tests/browser && npm install --silent
	node tests/browser/nav.mjs out

# Every browser test that needs only local files (test-pairs needs a CDN or `pairs-local`).
test-browser-all: test-browser test-playwright test-anim test-plain-anim test-nav test-keys test-labels test-anim-ref
