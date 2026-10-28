# agda-slides

Scientific slide decks, diagrams and animations as small typed languages in Agda
(`--safe --without-K`): free monads over containers, meaning given by algebras.  Goals: a
Container/FreeMonad-based DSL for high-quality scientific decks, exported to JS slides, plain
HTML and other backends.

The library is being rebuilt from first principles; start with `docs/Objects.md` (what the
objects are and how they relate) and `plan/Rebuild.md` (the order of work).  The previous
implementation is the git tag `legacy` and is checked out read-only at
`../agda-slides-legacy`; `docs/Legacy.md` says where its proofs live.

Needs Agda 2.7, the standard library 2.3, agda-categories, and the `parsnip` submodule.
`make check` typechecks everything under `src/`.
