# Plan

What is open. How the library works, and why, is in `docs/Design.md`; the command
reference is `docs/Authoring.md`. Finished work is not listed here (see `git log`).

## Next

1. **Animations** (built: syntax, `dur`, timelines, footprints, tracks and easings,
   playback in reveal; see `plan/Animations.md`). Left: the optional CSS-transition
   emitter, the reverse theorem for `Bezier` (approximate), other backends for
   `animation`, the Pairs deck's random point-pairs canvas.
2. **Use the generic `Container.*` theory for `Dia`.** Done: `Slides.Diagram.Generic` and
   `Slides.Anim.Generic` show that `fold` and `foldA` are the generic fold
   (`fold-agrees`). Left: the lemma that folding after `mapDia` is folding with a
   pulled-back algebra, from `Container.Lowering`/`Interpret` fusion (`mapDia` is a
   translation along a container morphism only up to the scalar), and monad laws for
   `Dia`-with-holes if templates are wanted.
3. **Laws left over for diagrams** (`Slides.Diagram.Laws`):
   - `Valid` (non-negative size) is a hypothesis of the unit laws; prove that every
     operation preserves it. This needs an ordered-ring record built on stdlib's
     `IsJoinSemilattice` (stdlib has no ordered ring).
   - `↔ m ∥ ↔ n ≈ ↔ (m + n)`.
   - State the monoid laws on `Dia` terms (`fold α (a ∥ b)`), not only on the
     layout combinators.
   - A scalar whose equality is not `_≡_` (a constructive real, or ℚ as unreduced
     pairs) as the first real test of the setoid generalisation.
   - Square roots and shapes on anchors (a `Shape` with ports taken from the
     outline, so arrows to a disc end on the circle; needs a `SqrtField` tier, with
     an error tolerance in any law that mentions the root).
   - Open diagrams `DiagramC S ⋆ X` with `>>=`, only if decks want first-class
     templates; the substitution lemma `fold (d >>= f) = fold′ (fold ∘ f) d` goes
     with it.
4. **Authoring.** Captions and numbering for figures and tables, with citation
   numbering (state threaded through the fold); warn about declared-but-unused
   resources; a proof that printed formulas have balanced braces.
5. **Backends.** Beamer/LaTeX, with `supports`/`uses` and the first lowerings
   (`placed` → flowed box, `diagram` → TikZ); then PDF, Markdown, pptx; watch mode.
6. **Generic stretch.** Fullness and faithfulness of `Poly-⇒`; naturality of the sum
   isomorphism in the setoid argument; indexed containers for typed slide state;
   layout as a symmetric monoidal structure.

## Risks

- **Submodule.** parsnip is pinned by the submodule commit; builds need
  `git submodule update --init`.
- **Library drift.** The README records the agda-categories commit and Agda version
  used (`c2e7c13e`, 2.7.0.1).
- **Typechecking time.** `make check` is about 90 s; keep instance search out of the
  core (see "No instance search" in `docs/Design.md`).
