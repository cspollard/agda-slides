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

# Golden-file test for the example deck (run `make example` first).
.PHONY: test test-browser
test:
	diff -u tests/golden/intro.index.html out/intro/index.html
	diff -u tests/golden/intro.init.js out/intro/init.js
	diff -u tests/golden/slides.css out/intro/slides.css

# Load the rendered deck in headless Chrome (set CHROME to override the binary).
test-browser:
	python3 tests/check_reveal.py out/intro/index.html
