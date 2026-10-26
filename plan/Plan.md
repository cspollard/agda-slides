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
   - *Keyframes and diffs.* Done (`Slides.Diagram.Delta`, shipped in `data-deltas`: round
     trip `patchL (diffL a b) a ≡ b`, `replay-deltas`). Numbers are shipped as differences
     from the old ones (trailing zeros dropped) and the JSON collapses runs of unchanged
     elements: the Pairs page is 1.47 MB → 0.24 MB. The page
     player is checked against Agda (`make test-anim-ref`: every frame the player rebuilds
     equals the frame Agda computed, on a steps animation and a 64-frame loop); the page
     player is one file, `assets/animation.js`, loaded by both backends (reveal's `init.js` and
     `plain.js` hold only glue). A *proof*
     about JavaScript is out of reach; stage 2 shrinks what the player has to be trusted with.
   - *Parametric bodies* (built; see `docs/Design.md`, "Animations"). `Slides.Diagram.Expr`:
     `Expr V = ExprC ⋆ V`, the free `Ops`-algebra (a free monad) over variables, with
     `evalWith O ρ` its fold, an `Ops`-homomorphism by `refl` (`evalWith-hom`), and `subst`
     the fold into `exprOps` (a homomorphism too, `evalWith-subst`). `Slides.Diagram.LayoutNatural`:
     `layout-natural`, `mapLayout h (layout_S d) ≡ layout_T (mapDia h d)` for an `IsOpsHom`
     `h` (six equations, no order, no condition on `-`), proved for every operation of
     `Place`; `layout-eval`, `layout-subst`. `SegBody S = blackBox (ℚ → Dia S) | template
     (Dia (Expr ⊤))` (the type is `SegBody`, not `Body`, which `Slides.Core` has; the
     constructor is `blackBox`, `opaque` being an Agda keyword), `bodyAt O`, `tweenT`; `hold`
     and `tween` build `blackBox`, `none` (padding) is a template. `Slides.Anim.Param`
     numbers the segments, renames each template's parameter to its own variable, and lays
     out the animation's frames once, symbolically (`atop` for `Par`, as in the timeline);
     `leaf-agrees` proves a segment's symbolic layout evaluates to its instance. When every
     segment is a template `render`/`renderLoop` emit `paramAnimation`, and the backend ships
     `data-param` (formulas grouped into phases, per-segment parameters) with a 30-line
     evaluator in both players; otherwise the delta encoding, byte for byte as before.
     `make test-anim-ref` checks every tick of five template animations (a slide, a 60-tick
     slide, grow/shrink with percent, monus and maximum, `Par` of unequal lengths, `par` with
     `none` padding) against the frames Agda computes from the functions; the intro deck's
     slider is a template.
     Left:
     - *The assembly of whole frames is tested, not proved*: that the frame at tick `k` is
       the layout at the assignment `i ↦ (parameter of segment i at tick k)` follows from
       `leaf-agrees` and `atop` commuting with `mapDia`, by an induction over the animation
       that tracks tick offsets (`merge`, `++`, `replicate`); that induction is not written.
     - Bodies that need division, remainder or comparison of the parameter (the point-pair
       loops, `Pairs`) stay flipbook until `Expr` grows those, each with its homomorphism
       proof; `animateBoth` is still always a flipbook.
     - `toℕ` of `exprOps` is the value at the all-zero assignment (it is not part of
       `IsOpsHom`; layout never applies it).
   - *Continuous time* (built). A template animation ships the tracks (pieces with easings)
     and the symbolic layout; the page evaluates at the real time of each
     `requestAnimationFrame` (`Slides.Anim.Continuous`, `Slides.Diagram.NatQ`/`ExprQ`; players
     in `assets/animation.js`). Size is independent of the tick count. Proved:
     `sampleAt-ι`, `leafAt-ι`, `leaf-tick` (with `Faithful`), `parAt-time`, `seqAt-*`,
     `animAt-dur`, `piece-hold`, `piece-start`. Tested only: the JavaScript (float easings,
     evaluator) against exact `frameAt` at every tick and quarter tick.
     Left: the assembly (`frameAt a τ` is the symbolic layout of tick `⌊τ⌋` at each
     segment's sample at `τ - start`) and the whole-timeline form of `leaf-tick`
     (needs `atop` to commute with `ι`); a template whose differences go negative draws a
     negative size (no clamping in the page); black-box bodies stay discrete.
   - *`Expr` through the generic theory.* `Slides.Diagram.Expr` is already `ExprC ⋆ V`;
     route `evalWith` through `Container.FreeMonad.Algebraic` (`fold-agrees`, as in
     `Slides.Diagram.Generic`), `subst` as `_>>=_`, `rename` as `fmap`, with the monad laws
     from `Container.FreeMonad` (`Eq`, `bind-cong`, `join-assoc`).
   A CSS-transition emitter does not belong here: it adds smoothness, not compression.
3. **Use the generic `Container.*` theory for `Dia`.** Done: `Slides.Diagram.Generic` and
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
