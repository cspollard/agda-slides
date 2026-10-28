# Minimal while the library is rebuilt (plan/Rebuild.md).  The legacy Makefile, with the
# example, golden and browser-test targets that return in step 7, is at
# ../agda-slides-legacy/Makefile.
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

clean:
	rm -rf _build build html
