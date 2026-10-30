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
- [ ] Compilation time: measure first (`n / 1` made `Hom` exponential); pairs with setoid equality.

## Theory
- [ ] Setoid equality throughout the scalar theories (unnormalised ℚ as a model); the theory records state their laws with `≡`; make them setoid-based (laws up to a carried equivalence, folds into setoids via the `Container` setoid algebras) so that models with non-canonical representatives fit, e.g. an unnormalised ℚ that defers gcd cost (it made `Hom` exponential when `ι n` was `n / 1`).  Measure where ℚ arithmetic is slow first; lighter fixes: literals in coprime form, fixed-denominator scalars.
- [ ] The open theorems in `docs/Dropped.md`: loop law, example-level agreement, coupling exactness at ticks, scene-level footprint, key-table soundness.
- [ ] 3D: orthogonality of `tangent` (c² + s² = 1) and invariance of `cis` under full turns; both need ℚ lemmas stdlib lacks (a floor lemma for `(a + d) / d`).
- [x] 3D: `pitch`, `box`, `cylinder` and the cube example (`make tensor`).
- [ ] 3D, optional: a shared `labelAt`, perspective, an `Anim` hook (`plan/3D.md`).
- [ ] Discharge `PctDigital`; halving for centring; `Min` and `ModBy` nodes.
- [ ] Non-isotropic scaling as a connective with smeared text (on hold).
- [ ] Generated JS evaluator, so that `assets/animation.js` is one table rather than tested by hand.
