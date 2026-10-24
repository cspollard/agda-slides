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
