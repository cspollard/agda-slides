AGDA ?= agda

.PHONY: check clean

# Typecheck every module under src/ and examples/.
check:
	$(AGDA) src/Slides.agda
	@for f in $$(find src -name '*.agda' ! -name Slides.agda); do $(AGDA) $$f || exit 1; done

clean:
	find . -name '*.agdai' -delete
	rm -rf MAlonzo _build out
