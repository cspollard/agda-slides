# agda-slides

A DSL, written in Agda, for producing scientific slide decks. A deck is a program in the free monad over a container of slide commands. Backends (HTML, reveal.js, …) are algebras for the container's polynomial functor, and the interpreter is the unique fold out of the free algebra. Proofs use [agda-categories](https://github.com/agda/agda-categories).

See `Goals.md` for the goals and `plan/Plan.md` for the roadmap.

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

## Layout

- `src/Container/` — generic, slide-independent development: containers as polynomial functors on `Setoids`, the free monad, its algebraic description, and interpretation/fusion. Nothing here imports `Slides.*`.
- `src/Slides/` — the slide DSL (to come).
- `parsnip/` — submodule: verified XML/JSON/SVG printers and parsers with proved round trips, used for HTML output (`plan/HTML.md`).
- `plan/` — roadmap and detailed plans.
