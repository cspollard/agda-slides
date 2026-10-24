AGDA ?= agda

.PHONY: check clean

# Typecheck every module under src/ and examples/.
check:
	$(AGDA) src/Slides.agda
	@for f in $$(find src -name '*.agda' ! -name Slides.agda); do $(AGDA) $$f || exit 1; done

clean:
	find . -name '*.agdai' -delete
	rm -rf MAlonzo _build out

# R0 spike: write out/spike/{index.html,init.js}.  REVEAL points at an
# unpacked reveal.js distribution (e.g. `npm install reveal.js`).
REVEAL ?= $(CURDIR)/node_modules/reveal.js

.PHONY: spike
spike:
	mkdir -p out/spike _build/spike
	ln -sfn $(REVEAL) out/spike/reveal
	$(AGDA) --compile --compile-dir=_build/spike src/Slides/Spike/Reveal.agda
	mv Reveal _build/spike/Reveal 2>/dev/null || true
	_build/spike/Reveal
	cp assets/slides.css out/spike/slides.css

# Render the example deck to out/intro/.
.PHONY: example
example:
	mkdir -p out/intro _build/example
	ln -sfn $(REVEAL) out/intro/reveal
	cp assets/slides.css out/intro/slides.css
	$(AGDA) --compile --compile-dir=_build/example src/Slides/Examples/IntroMain.agda
	mv IntroMain _build/example/IntroMain 2>/dev/null || true
	_build/example/IntroMain

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
	diff -u tests/golden/plain.js out/plain/plain.js
	diff -u tests/golden/plain.css out/plain/plain.css

# Load the rendered deck in headless Chrome (set CHROME to override the binary).
test-browser:
	python3 tests/check_reveal.py out/intro/index.html
	python3 tests/check_reveal.py out/talk/index.html
	python3 tests/check_plain.py out/plain/index.html
	python3 tests/check_reveal.py out/showcase/index.html
	python3 tests/check_plain.py out/showcase-plain/index.html

# Render the component-based example deck to out/talk/.
.PHONY: talk
talk:
	mkdir -p out/talk _build/talk
	ln -sfn $(REVEAL) out/talk/reveal
	cp assets/slides.css assets/plot.svg out/talk/
	$(AGDA) --compile --compile-dir=_build/talk src/Slides/Examples/TalkMain.agda
	mv TalkMain _build/talk/TalkMain 2>/dev/null || true
	_build/talk/TalkMain

# Render the component-based deck as standalone HTML to out/plain/.
.PHONY: plain
plain:
	mkdir -p out/plain _build/plain
	cp assets/plain.css assets/plain.js assets/slides.css assets/plot.svg out/plain/
	$(AGDA) --compile --compile-dir=_build/plain src/Slides/Examples/PlainMain.agda
	mv PlainMain _build/plain/PlainMain 2>/dev/null || true
	_build/plain/PlainMain

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

# Render the showcase deck with both backends to out/showcase/ and out/showcase-plain/.
.PHONY: showcase
showcase:
	mkdir -p out/showcase out/showcase-plain _build/showcase
	ln -sfn $(REVEAL) out/showcase/reveal
	cp assets/slides.css assets/plot.svg out/showcase/
	cp assets/plain.css assets/plain.js assets/slides.css assets/plot.svg out/showcase-plain/
	$(AGDA) --compile --compile-dir=_build/showcase src/Slides/Examples/ShowcaseMain.agda
	mv ShowcaseMain _build/showcase/ShowcaseMain 2>/dev/null || true
	_build/showcase/ShowcaseMain

# Drive the rendered showcase deck in a real browser (keyboard, fragments, config).
# Needs `make showcase` first and `npm install` in tests/browser once.
.PHONY: test-playwright
test-playwright:
	cd tests/browser && npm install --silent
	node tests/browser/run.mjs out
