# TODO

Living list for the rebuilt library (design in `docs/Objects.md`, history in `plan/Rebuild.md`,
dropped legacy theorems in `docs/Dropped.md`).  Order: simplify first, then 3D, then features.

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
- [ ] `Slides.Trig` and a 3D front end compiling to `Dia`, extracted from `Examples/ATLAS.agda` (plan in `plan/3D.md`).

## Phase 3: features
- [ ] Line breaks, native text colours and styles, nested bullets (through the shared drawing vocabulary; design note first).
- [ ] Background image; PNG and PDF primitives (how to ship: copy into `out/`; what Plain does).
- [ ] Slide number for the Plain backend (Reveal has it); decide per-slide command versus deck option, and stacks.
- [ ] README and module-level documentation with geometric intuition, written as each module is touched.
- [ ] Compilation time: measure first (`n / 1` made `Hom` exponential); pairs with setoid equality.

## Theory
- [ ] Setoid equality throughout the scalar theories (unnormalised ℚ as a model); see `plan/Rebuild.md`.
- [ ] `docs/Dropped.md` gaps 5–12: `Repeat` periodicity, scene-level `Par` commutativity over layouts, example-level agreement, coupling exactness at ticks, key-table soundness.
- [ ] Discharge `PctDigital`; Bézier easing; `Min` and `ModBy` nodes.
- [ ] Non-isotropic scaling as a connective with smeared text (on hold).
- [ ] Generated JS evaluator, so that `assets/animation.js` is one table rather than tested by hand.
