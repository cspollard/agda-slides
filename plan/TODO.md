# TODO

Living list for the library (design in `docs/Objects.md`, working rules in `docs/Contributing.md`,
open legacy theorems in `docs/Dropped.md`).  Order: simplify first, then 3D, then features.

## Done
- [x] Rebuild (steps 0–10): scalar theories, `Diagram`, `Scene`, `Program`, `Deck`, backends, all decks, goldens and browser tests.
- [x] Polyline and ellipse primitives; `.Convenience` geometric operators.
- [x] Reveal slide number: `RevealConfig.slideNumber`.
- [x] `figure` against declared resources: `Checked R` in `Deck/DSL.agda`.
- [x] Repository clutter: step branches and worktrees removed (archive tags remain).

## Phase 1: simplification and consolidation
- [ ] Deck DSL: state each primitive once (`fragment`, `fragmentWith`, `figure*` are declared at the flow level and lifted again at body level).  Branch `simplify-dsl`.
- [ ] Share the LHC tables between `LHC.agda` and the Collider deck (about 21 KB shipped twice).  Branch `simplify-lhc`.
- [ ] Stylesheets: drop dead and duplicated rules, generate what an Agda record already determines, light highlight theme on white slides.  Branch `simplify-css`.
- [ ] Rewrite this file as work lands (this item).

## Phase 2: 3D
- [x] `Slides.Trig` and `Slides.Three.*` (view, solids, render) compiling to `Dia`, extracted from `Examples/ATLAS.agda` (what remains: `plan/3D.md`).

## Phase 3: features
- [x] One shared text tree (`Slides.Text`), `br`, `styled`, `sub`/`sup` in prose, nested bullets (design in `docs/Objects.md`).  Cost: about +240 lines in `src/`, over budget.
- [ ] Text follow-ups: measure a styled run's size and weight; fix the `dy` of a label line after a sub/superscript (changes existing label bytes); ship the text tree as JSON instead of the markup string, deleting `markup` and the string syntax; `styled` and `br` in animated labels (now plain text and a space); prove `plain` of a parsed label is the label minus markup.
- [ ] Background image; PNG and PDF primitives (how to ship: copy into `out/`; what Plain does).
- [ ] Slide number for the Plain backend (Reveal has it); decide per-slide command versus deck option, and stacks.
- [ ] README and module-level documentation with geometric intuition, written as each module is touched.
- [x] Compilation time: measured, not slow (loading dominates).
- [x] Collider run time (40 s to about 19 s to about 10 s): sharing looked entries up linearly by decidable equality; `Slides.Backend.Share` now uses an AVL index (validated hint, proof unchanged).  Then measured by stubbing, not guessed: interning was never the main cost (only ~10 000 tree nodes, ~4 000 distinct).  The deck's own `_⊓_` on ℕ recurses on the value (millions), 7 s; replaced by built-in subtraction.  `ship` was quadratic (a `where` definition is lifted and recomputed at every use, so its use counts were rebuilt per position); it is now one pass with indexed maps.  Left (~4 s over a 5.7 s floor): interning lookups, rendering, and the Title animation's terms.  Sharing before the events are expanded is no longer worth it.

## Theory
- [ ] Setoid equality throughout the scalar theories (laws up to a carried equivalence; non-canonical models such as an unnormalised ℚ): planned, wanted for the mathematics, not a speed-up (`plan/Rationals.md`).  Until then raw `ℚᵘ` arithmetic is usable as is.
- [x] Plots: axes, marks, log axes, ratio panel, reveal/morph, CSV in (`docs/Plots.md`, history and follow-ups in `plan/Plots.md`; on branch `plots`).
- [ ] The open theorems in `docs/Dropped.md`: loop law, example-level agreement, coupling exactness at ticks, scene-level footprint, key-table soundness.
- [ ] 3D: orthogonality of `tangent` (c² + s² = 1) and invariance of `cis` under full turns; both need ℚ lemmas stdlib lacks (a floor lemma for `(a + d) / d`).
- [x] 3D: `pitch`, `box`, `cylinder` and the cube example (`make tensor`).
- [ ] 3D, optional: perspective, an `Anim` hook (`plan/3D.md`).
- [ ] Discharge `PctDigital`; halving for centring; `Min` and `ModBy` nodes.
- [ ] Non-isotropic scaling as a connective with smeared text (on hold).
- [ ] Generated JS evaluator, so that `assets/animation.js` is one table rather than tested by hand.
