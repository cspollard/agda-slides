# agda-slides

A DSL, written in Agda, for producing scientific slide decks. A deck is a program in the free monad over a container of slide commands. Backends (HTML, reveal.js, …) are algebras for the container's polynomial functor, and the interpreter is the unique fold out of the free algebra. Proofs use [agda-categories](https://github.com/agda/agda-categories).

See `Goals.md` for the goals, `docs/Authoring.md` for how to write a deck, and `plan/Plan.md` for the roadmap.

## Requirements

- Agda 2.7.0.1
- `standard-library` and `agda-categories`, both registered in `~/.config/agda/libraries` (developed against agda-categories commit `c2e7c13e`)

## Getting the sources

`parsnip/` is a git submodule:

```
git clone --recurse-submodules <url>
# or, in an existing clone:
git submodule update --init
```

## Building

```
make check
```

typechecks every module under `src/`.

## Rendering the example deck

```
npm install reveal.js            # or point REVEAL at any reveal.js distribution
make example                     # writes out/intro/index.html and init.js
make talk plain                  # component-based deck: reveal.js (out/talk) and standalone HTML (out/plain)
make test                        # golden-file diffs
make test-browser                # headless Chrome check (set CHROME to override)
make showcase                   # every feature, with both backends (out/showcase, out/showcase-plain)
make test-playwright             # drive the showcase in a real browser (needs `npm install` in tests/browser, done by the target)
make test-negative               # decks citing undeclared resources must not typecheck
make check-resources             # declared figures exist next to the rendered decks
```

Open `out/intro/index.html` in a browser. `make spike` builds the R0 spike (`plan/HTML.md`).

## Layout

- `src/Container/` — generic, slide-independent development: containers as polynomial functors on `Setoids`, the free monad, its algebraic description, and interpretation/fusion. Nothing here imports `Slides.*`.
- `src/Slides/` — the slide DSL (to come).
- `parsnip/` — submodule: verified XML/JSON/SVG printers and parsers with proved round trips, used for HTML output (`plan/HTML.md`).
- `plan/` — roadmap and detailed plans.
