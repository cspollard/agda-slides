# Working on the library

Design: `docs/Objects.md`.  Open work: `plans/TODO.md`.  Theorems of the previous implementation
that are not yet restated: `docs/Dropped.md`.

## Rules for every change
- **Principled.**  A nontrivial type is a free algebra of a signature, its meanings are folds, and
  its relations to other types are lowerings and homomorphisms.  Prove identity and composition
  laws and general invariants where the structure is stated; generic facts go in `Container.*`,
  never per language.  Derive lemmas from the laws of a theory, not by computing in ℚ; state model
  facts as named hypotheses.
- **No `rewrite`.**  Write proofs as `cong`/`cong₂`/`trans` chains or `≡-Reasoning`, or derive
  them from a generic lemma (`pfold-cong`, `tabulate-cong`, ...); use `subst` only where a type
  must change.  `rewrite` hides which equation is used and breaks when terms are restated.  New
  code adds none; code that is touched loses its uses.
- **Small.**  Say a line budget up front.  A change that exceeds it, or adds more than it
  deletes, stops and reports before continuing.
- **Gate.**  `make check` clean (no postulates, no unsolved metas, no instance search in core,
  no `|| true`); for visible changes also build the decks and run `make test`, with goldens
  byte-identical unless the change is about the output.
- **Report.**  Lines added and deleted per module, check time, the laws proved with their
  statements, anything postulated or deferred.

## Working in parallel
One agent, one git worktree, one branch off `main`, disjoint files.  Brief an agent with
`docs/Objects.md`, this file and the task.  Give logs and scripts unique names (scratch space is
shared).  A worktree needs a plain copy of `parsnip/src`, not a submodule checkout.

## Tooling
Bash calls cap near two minutes: run long builds in the background with a log.  macOS has BSD
`sed` (use `sed -E`, or Python) and no `timeout`.  `npm install` in `tests/browser` before the
browser tests.  Never `git add -A`.

## The previous implementation
Git tag `legacy` holds it, `legacy-collider` the same plus the Collider deck, and `archive/*`
the abandoned spikes.  Look there only for a theorem listed in `docs/Dropped.md`, with
`git worktree add ../agda-slides-legacy legacy`, and port the statement against the new
definitions; do not copy definitions and do not read it to learn the design.
