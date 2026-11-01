# TODO

Living list for the library (design in `docs/Objects.md`, working rules in `docs/Contributing.md`,
open legacy theorems in `docs/Dropped.md`).  Order: simplify first, then 3D, then features.

## Done
- [x] Rebuild (steps 0–10): scalar theories, `Diagram`, `Scene`, `Program`, `Deck`, backends, all decks, goldens and browser tests.
- [x] Polyline and ellipse primitives; `.Convenience` geometric operators.
- [x] Reveal slide number: `RevealConfig.slideNumber`.
- [x] `figure` against declared resources: `Checked R` in `Deck/DSL.agda`.
- [x] Repository clutter: step branches and worktrees removed (archive tags remain).

## Review plan (`plans/Review.md` §9)
- [x] Phase 1, container spine (b05e69d..763437f, −297 lines against −350).
- [x] Phase 2, theories on stdlib structures (78f3403, +23 against −60).
- [x] Phase 3, Diagram tag/payload split, `Draw.group` removed, functoriality derived (e9bf14d..67a4c31, −2 against −250).
- [x] Phase 3 left over: layout as a `NaturalTransformation` (§4.2) is not worth doing (`ι` is natural only on `OkDia`; `plans/Review.md` §9.1); the 17-way handler splits (`layoutCong`, `okOp`, `clean`, `digit`) are genuine per-operation handlers and stay (`soundness` too, Phase 11).
- [x] Phase 4, temporal algebra, scene setoid and Hudak axioms (ddaf6ef..3d7dbc8, +337 against −100).
- [x] Phase 4 left over: `Container.Tagged` for the Scene signature (`mapScene` laws), done in Phase 8; the rest of §5.4 stays open.
- [x] Phase 5, program behaviours, bisimulation ⇔ trace equality, `Via` as `mapMaybe` (589e306..79d3c10, −31 against −110).
- [x] Phase 5 left over: `F-Coalgebras` category for machines (done in Phase 9 S1, `Semantics.Behaviour.final`); `skip-inject`/`lower-supported` stay direct.
- [x] Phase 7, small duplicates (−47 in `src/` against −150; skipped items in `plans/Review.md` §9).
- [x] Phase 6, content as containers (7d2d405..529df14, +177 against −300).
- [x] Phase 8 (§4.3, Phase 4/6 leftovers): size into envelope semigroups, layout `Action`/`Placement`, `IsSemigroup`/`Monoid` packaging, `cut`; scene signature on `Container.Tagged`; `FlowLowering` rename; the former `Program/Embed` module folded into `Scene.Animation` (no longer a module); `toLaTeX-bind`; `glueMonoid` and `chunks` as `IsMonoidHomomorphism` (+238; 23 `rewrite` removed).
- [ ] Left: `_≈ᵖ_` as a permutation `Setoid` with `atop` commutative; `Overlay` on stdlib structures and out of `Diagram`; `Natural` offsets per connective.
- [x] No `rewrite` (`docs/Contributing.md`): the read-only audit listed 99 uses in 22 files, in five batches (Phase 9 below).  Line budgets are a tripwire; clarity and robustness justify overshoot.

## Phase 9: how the objects relate (`plans/Review.md` §9.1, `docs/Objects.md` "How the objects relate")
- [x] (a) Docs: how the objects relate (forms, sections and retractions, statuses) and where things live, in `docs/Objects.md`; layers in `src/Slides.agda`.
- [x] (b) S1: `lower-copairL-inl` in `Container.Sum.Properties` (`lower-inject`, `skip-inject` its instances); `Semantics.Behaviour` (`final : Terminal (F-Coalgebras Moore)`, `mapO`, `reindex`, `const`/`hd`, `hd∘const`); `Program/Machine` a coalgebra view (`coalg`), `Program/Sem` on the layer, no `rewrite`.  Not done: `sem-inject` generic in the signature (one instance only).
- [x] (c) S4: one notion of step (`Deck.Steps`: a step is a page fragment), `ticks`/`visible`/`deckM`/labels/`render-events` count it; `deckM` is `visible (flat d)` reindexed along `pos` (`feed-deckM`).  The step-count bug is fixed in the model.
  - [x] `render-fragments` holds given `BlockLaw`: proved in Phase 10, `BlockLaw` is now `block-count` under the decidable `saneSlide`, discharged for every shipped deck.
  - [ ] `visible` is chunk-granular; fragments inside a chunk would need a reveal operation on flows.
  - [x] `Steps.aside?` duplicates `Render.aside?`: `Render` imports it (Phase 10).
- [x] (d) S5: `Framed W H` with `framedMonoid` (up to layout), `renderF`, `marks-hom` (the marks layer, for fixed axes, a monoid homomorphism from series lists).  Plot content stays `List Series` (lowering per `Geo`, legend entries); an extension only if diagram annotations in plots are wanted.  Dead `lerp-same`, `niceStep` removed.
  - [x] `Framed` is generic to Diagram: `Slides.Diagram.Framed`, over any `Space` (Phase 10).
- [x] (e) `rewrite` batches 2 (`Diagram/Natural`, 27) and 3 (`Valid`, `Convenience/Properties`, `Commute`, `Names`, `Names/Soundness`, 20): none left; `placed-unitˡ`/`placed-unitʳ`, shared `validMonoid`.
  - [x] `⊔-idem` moved to `Scalar/Core` (Phase 10).
- [ ] (f) Later (Phase 10 did the `rewrite` batches and most of the clarity audit):
  - S2: models layer (theories as data, powers are models, Hudak laws for programs) and the read-at-start retraction law, only if the conditional laws stay small.
  - S3: the deck behaviour stated once (`deckBeh`), `pause-agree` restated against it.
  - [x] Clarity audit, closed in Phase 11: `Names/Soundness` stays a hand induction **[decided]** (`Draws` mentions the child's layout, so it is not a plain fold, and a catch-all handler clause is stuck on a variable operation, so `pfold-rel` moves the 17-way split into the hom and `clean` without removing it); `chunks-isMonoidHomomorphism` kept as the documented law (`render-glue` needs only its `homo` field, `chunks-++`).
  - `visible` below chunk granularity (a reveal operation on flows).

## Phase 10: page steps proved, last `rewrite`s, clarity (`plans/Review.md` §9.2)
- [x] `BlockLaw` proved: `Backend/Fragments` (counting `.fragment`), `Render/{Inline,Sane,Svg,Properties}`; `render-fragments` and `ticks-fragments` given the decidable `saneSlide` (class strings, `language-` classes, draw style classes); `Render/Shipped` checks every shipped deck by `tt`.
- [x] SVG condition on the layout's style classes (`svg?`), not the printed output; `Diagram.Print` and `animationEl` pieces lifted to top level, so `renderSVG-count` is proved against the real definitions (no mirror).
- [x] `rewrite` batches 1, 4, 5: Scene (18, via `holdC-≤`/`delayC-≤`/`seqC-≤`, `seq-assoc-pt′`, `duration-nonneg`), Scalar, `Share/Properties`, Program/Supports and Navigation (22).  `grep -w rewrite src` is empty.
- [x] Clarity: `InlineC`/`MathC` as `Tagged Fin`; `map-fuse`; `mapXY` with `Diagram.DrawLaws`; `Diagram.Framed`; dead `deckOf`, `kids`, `noSupports` removed; `Deck/Lower` header fixed.

## Phase 1: simplification and consolidation
- [x] Deck DSL: each content command stated once (`Prims` in `Deck/DSL.agda`, commit 82a3f05).
- [x] LHC tables: checked, no duplication (`Collider` imports `lhcAnim` and `triggerAnim` from `LHC.agda`; the built deck repeats nothing).  The old "21 KB shipped twice" was the combined source size.
- [x] Stylesheets: checked, 8 KB in all; the numbered classes (`ph*`, `plot-s*`, `tilt-*`) are generated, nothing dead to drop.
- [x] Rewrite this file as work lands.

## Phase 2: 3D
- [x] `Slides.Trig` and `Slides.Three.*` (view, solids, render) compiling to `Dia`, extracted from `Examples/ATLAS.agda` (what remains: `plans/3D.md`).

## Phase 3: features
- [x] One shared text tree (`Slides.Text`), `br`, `styled`, `sub`/`sup` in prose, nested bullets (design in `docs/Objects.md`).  Cost: about +240 lines in `src/`, over budget.
- [ ] Text follow-ups: measure a styled run's size and weight; fix the `dy` of a label line after a sub/superscript (changes existing label bytes); ship the text tree as JSON instead of the markup string, deleting `markup` and the string syntax; `styled` and `br` in animated labels (now plain text and a space); prove `plain` of a parsed label is the label minus markup.
- [ ] Background image; PNG and PDF primitives (how to ship: copy into `out/`; what Plain does).
- [ ] Slide number for the Plain backend (Reveal has it); decide per-slide command versus deck option, and stacks.
- [ ] README and module-level documentation with geometric intuition, written as each module is touched.
- [x] Compilation time: measured, not slow (loading dominates).
- [x] Collider run time (40 s to about 19 s to about 10 s): sharing looked entries up linearly by decidable equality; `Slides.Backend.Share` now uses an AVL index (validated hint, proof unchanged).  Then measured by stubbing, not guessed: interning was never the main cost (only ~10 000 tree nodes, ~4 000 distinct).  The deck's own `_⊓_` on ℕ recurses on the value (millions), 7 s; replaced by built-in subtraction.  `ship` was quadratic (a `where` definition is lifted and recomputed at every use, so its use counts were rebuilt per position); it is now one pass with indexed maps.  Left (~4 s over a 5.7 s floor): interning lookups, rendering, and the Title animation's terms.  Sharing before the events are expanded is no longer worth it.

## Theory
- [ ] Setoid equality throughout the scalar theories (laws up to a carried equivalence; non-canonical models such as an unnormalised ℚ): planned, wanted for the mathematics, not a speed-up (`plans/Rationals.md`).  Until then raw `ℚᵘ` arithmetic is usable as is.
- [x] Plots: axes, marks, log axes, ratio panel, reveal/morph, CSV in (`docs/Plots.md`, history and follow-ups in `plans/Plots.md`; merged to main).
- [x] Smooth curves: the `Function` extension (`CurveC`, `Dia⁺`, sampling lowering to one Bézier `Path`, `exact` mark; `plans/Plots.md`).  Left: adaptive sampling, the ε-approximation contract `Within` (stated, not proved).
- [ ] The open theorems in `docs/Dropped.md`: loop law, example-level agreement, coupling exactness at ticks, scene-level footprint, key-table soundness.
- [ ] 3D: orthogonality of `tangent` (c² + s² = 1) and invariance of `cis` under full turns; both need ℚ lemmas stdlib lacks (a floor lemma for `(a + d) / d`).
- [x] 3D: `pitch`, `box`, `cylinder` and the cube example (`make tensor`).
- [ ] 3D, optional: perspective, an `Anim` hook (`plans/3D.md`).
- [ ] Discharge `PctDigital`; halving for centring; `Min` and `ModBy` nodes.
- [ ] Non-isotropic scaling as a connective with smeared text (on hold).
- [ ] Generated JS evaluator, so that `assets/animation.js` is one table rather than tested by hand.
- [ ] Curves, later: slopes for `Function` (`plans/Plots.md`, "Smooth curves").  Today the lowering takes Fritsch-Carlson slopes from the samples (about h³ error, no overshoot).  Options: an optional `f′` on `Function` (exact slopes, contract "f′ is the derivative of f" as a named hypothesis, fall back to samples); central differences on `f` itself (about h⁴); forward-mode AD over dual numbers if `f` becomes polymorphic in the scalar (brings back `Set₁`).  Differentiability is never a type: at most a hypothesis in the `Within` law.  Also: SVG `S`/`s` shortcuts and relative coordinates to cut the Bézier path's size by about a third.
- [ ] Possible, not required: a parametric `Function` (`γ : S → S × S`, the graph as the special case) for curves that are not graphs (ATLAS tracks, circles, spirals); closed variant for filled arcs.  Little size gain (the ATLAS deck has 6 short polylines); worth it only for such curves.  Other `Function` follow-ups: clipping inside `Function` (only `exact` in `Plot` clips), a ℕ sampler for `Dia ℕ` examples, converting `power` in `Examples/Plots.agda` to `exact` (regenerate its golden).
