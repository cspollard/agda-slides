# agda-slides

A DSL, written in Agda, for producing scientific slide decks. A deck is a program in the free monad over a container of slide commands. Backends (HTML, reveal.js, …) are algebras for the container's polynomial functor, and the interpreter is the unique fold out of the free algebra. Proofs use [agda-categories](https://github.com/agda/agda-categories).

See `Goals.md` for the goals and `plan/Plan.md` for the roadmap.

## Requirements

- Agda 2.7.0.1
- `standard-library` and `agda-categories`, both registered in `~/.config/agda/libraries` (developed against agda-categories commit `c2e7c13e`)

## Building

```
make check
```

typechecks every module under `src/`.
