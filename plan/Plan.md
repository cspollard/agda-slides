# Plan

What is open. How the library works, and why, is in `docs/Design.md`; the command
reference is `docs/Authoring.md`. Finished work is not listed here (see `git log`).

## Next

1. **Animations** (built: syntax, `dur`, timelines, footprints, tracks and easings,
   playback in reveal; see `plan/Animations.md`). Left: the optional CSS-transition
   emitter, the reverse theorem for `Bezier` (approximate).
2. **A JavaScript backend for animations** (the flipbook emits every frame as a full SVG:
   the Pairs deck's `index.html` is about 1.4 MB, mostly the two point-pair loops).
   Two stages, each with its proof:
   - *Keyframes and diffs.* Emit the first frame and, per frame, the attributes that
     change (frames of one animation share their structure). Law:
     `patch (diff a b) a ≡ b`, and playback of the encoded frames equals the flipbook.
   - *Parametric bodies.* Make a segment's body an open diagram (`DiagramC S ⋆ X`, with
     scalar expressions in the holes) instead of an opaque `ℚ → Dia S`; compile the track
     and the expressions to a small player that evaluates at any time (continuous time, size
     independent of the frame count). Theorem: the compiled player at tick `t` agrees with
     `frames` at `t` (`Slides.Anim.Generic`, one level up). Bodies that stay Agda functions
     keep the flipbook. This is also what the open-diagrams item below needs.
   A CSS-transition emitter does not belong here: it adds smoothness, not compression.
2. **Use the generic `Container.*` theory for `Dia`.** Done: `Slides.Diagram.Generic` and
   `Slides.Anim.Generic` show that `fold` and `foldA` are the generic fold
   (`fold-agrees`); `Slides.Diagram.MapFusion` shows `mapDia f` is translation along the
   container morphism `scalarMor f` (identity on positions), hence functorial up to
   equality of programs (`mapDia-id`, `mapDia-∘`) and `fold α (mapDia f d) ≈ fold (pull
   (scalarMor f) α) d` for congruent `α` (`fold-mapDia`). Left: monad laws for
   `Dia`-with-holes if templates are wanted; pulling `Layout` back along a scalar map
   needs the map to be an ordered-ring homomorphism (see `docs/Design.md`).
4. **Laws left over for diagrams** (`Slides.Diagram.Laws`):
   - Done in `Slides.Diagram.Valid` (for ℤ and ℚ, via an `IsOrdered` record: the sum keeps
     non-negativity, `fromℕ` is non-negative, `⊔` idempotent): every operation keeps a layout
     `Valid` (`valid-layout`: a term whose sized leaves are non-negative, `WellSized`, is valid;
     the hypotheses are needed, `invalid-rectangle`); `↔ m ∥ ↔ n ≈ ↔ (m + n)` (and `↕`, `⊙`);
     congruence of `besideA`/`aboveA`/`atop` in `≈ᴸ`; the associativity and unit laws on
     `Dia` terms; `margin 0 0 0 0 d ≈ d`.
   - Still open: `margin` composition (`margin a (margin b d) ≈ margin (a+b) d`: needs the
     shift of a layout by a gap), laws for `hcat`/`vcat` with several elements, and unit laws
     without `Valid` (false for a negative size, e.g. ℤ).
   - A scalar whose equality is not `_≡_` (a constructive real, or ℚ as unreduced
     pairs) as the first real test of the setoid generalisation.
   - Square roots and shapes on anchors (a `Shape` with ports taken from the
     outline, so arrows to a disc end on the circle; needs a `SqrtField` tier, with
     an error tolerance in any law that mentions the root).
   - Open diagrams `DiagramC S ⋆ X` with `>>=`, only if decks want first-class
     templates; the substitution lemma `fold (d >>= f) = fold′ (fold ∘ f) d` goes
     with it.
5. **Authoring.** Captions and numbering for figures and tables, with citation
   numbering (state threaded through the fold); warn about declared-but-unused
   resources; a proof that printed formulas have balanced braces.
6. **Backends.** Beamer/LaTeX, with `supports`/`uses` and the first lowerings
   (`placed` → flowed box, `diagram` → TikZ); then PDF, Markdown, pptx; watch mode.
7. **Generic stretch.** Fullness and faithfulness of `Poly-⇒`; naturality of the sum
   isomorphism in the setoid argument; indexed containers for typed slide state;
   layout as a symmetric monoidal structure.

## Risks

- **Submodule.** parsnip is pinned by the submodule commit; builds need
  `git submodule update --init`.
- **Library drift.** The README records the agda-categories commit and Agda version
  used (`c2e7c13e`, 2.7.0.1).
- **Typechecking time.** `make check` is about 90 s; keep instance search out of the
  core (see "No instance search" in `docs/Design.md`).
