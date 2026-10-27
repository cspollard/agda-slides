# Bloat audit

Audit of `src/` (16 267 lines, 121 modules at the start) for code that can be removed or
consolidated before the `plan/Unify.md` refactor (unify diagrams, animations and decks; input
machines; temporal container). Branch `bloat-audit`. "Stage" is the stage of `plan/Unify.md`
the item interacts with; items marked *refactor* are not touched here because that stage
reshapes the module (Anim.Syntax, Anim.Continuous*, Anim.Timeline*, Anim.Assembly*,
Anim.Track, Slides.Steps, Slides.Core, Slides.Lower, Container.Lowering).

Tools (not committed): a script that parses every `import`/`using`/`renaming` list and checks
each name against the rest of the module; a name scan that lists top-level signatures with no
other occurrence in `src/`, `tests/` or the docs; a 5-line-window duplicate scan. The name scan
over-reports (a use at the start of a line looks like a clause head, mixfix operators, instance
declarations, record fields), so every candidate was grepped by hand before removal.

## Done (see the commits)

### a. Unused imports (about 220 lines in 80 files)

Two passes to a fixed point: 62 modules in the first pass (the Properties split left most),
27 more after dropping empty `open import X using ()` lines. A `using ()` line only brings
instances into scope; each was removed and the module re-typechecked on its own, so only
those that were not needed went (the ones left are the `renaming (_,_ to _,ₚ_)` imports, which
rename a constructor and are used). `Σ-syntax`-style syntax names were never removed.
Risk: none (the type checker is the oracle). Stage: none.

### b. Dead definitions and modules

| where | what | lines |
|---|---|---|
| `Slides/Backend/XML.agda` | whole module (`XMLEndo`, `XMLTrees`): imported by `XML.Properties` and never used | 32 |
| `Anim/Phases.agda:109`, `Anim/DPhases.agda:27` | `encodeDraw`, `encodeDrawD` (only `encodeWith` is used) | 6 |
| `Diagram/Euclid.agda:114` | `exprD`, an unused injection (the other three are used) | 3 |
| `Backend/Common.agda` | `layoutAlg` and its module `L`; only `layoutα` is used | 6 |
| `Backend/Diagram.agda:97` | `points` | 3 |
| `Anim/Share/Properties.agda:218` | `evalNode-ext` (its siblings `evalArg-ext`, `evalOut-ext` are used) | 4 |
| `Container/Polynomial.agda:90` | `Poly-Endo`, an alias of `Poly` at `Level 0` | 4 |

No theorem was removed or renamed. Every top-level theorem in a `.Properties` module that
nothing imports (about 110, e.g. `Valid.gap-∥`, `Laws.combine-assoc`, `Expr.Properties.subst-assoc`,
`Footprint.Properties.footprint-swap`) was kept: they are the statements those modules exist for.

### c. Misplaced proof

`renderBody-bind` lived at the bottom of `Slides.Backend.Common`, an executable module (every
deck compiled it). Moved to the new `Slides.Backend.Common.Properties`, per the module
conventions; statement and name unchanged. `Slides.Components` pointed at `renderDeck-bind` in
the wrong module; fixed.

### d. Duplication replaced by shared helpers

* `Backend.Common`: `contentα` and `layoutα` were the same record at two shapes; now
  `commandα render`. The two copies of `cls` (fragment class) are `fragmentClass`.
* `Backend.HTML`: `scriptTag` and `stylesheet` were defined privately in both `Reveal` and `Plain`.
* `Backend.Diagram`: two local `Maybe` maps (`_▹′_`, `_▹_`) and four `maybeOr`-style helpers are
  `Data.Maybe.map` / `fromMaybe`.
* Makefile: the compile / `mv` / run triple of nine targets is one `run-main` macro; the plain
  deck's five asset files are `PLAIN_FILES`.

### e. Docs

`docs/Authoring.md` said `Slides.Diagram.Place.Layout` (it is `Slides.Diagram.Draw.Layout`);
README listed the removed `Backend/XML`; `docs/Design.md` module-conventions list lacked the theory
module `Backend.Restyle`; `plan/Animations.md` described `pairs.js` as present; `plan/TODO.md`'s last
item is done.

## Deferred (not touched)

### Cannot be removed, but misleading to a scanner
* `Slides.Anim.Loop`, `Slides.Anim.Assembly.Continuous`, `Container.Category`, `Slides.Backend.Restyle`
  are imported by nothing (not even `Everything` consumers) but are theory modules whose theorems are the
  point (looping is `t mod n`; the continuous assembly; the category of containers; restyling is a backend
  homomorphism). `Restyle` should arguably be `Backend.Restyle.Properties` or moved under a theory heading
  (about 77 lines; changing the module name is cheap but breaks the one doc reference). Stage: none.
* `Slides.Spike.Reveal` kept as documented.
* API with no user in `src/`: `DSL.animate`, `animateLoop`, `animateBoth`, `fragmentWith`;
  `Components.bulletBody`, `sectionSlide` (used in Talk only through `sectionSlide`; `bulletBody` unused);
  `Diagram.thick/dashed/faded/anchored`; `Slides.Lower.stripScripts`, `lowerBody`; `Backend.Reveal`
  `serifTheme`/`solarizedTheme`; `Slides.Literals` instances (needed by instance search, not dead).
  About 60 lines. These are the authoring vocabulary (docs mention most). Decide at Stage 3 (decks) when the
  DSL surface is reworked; `Lower`/`DSL` change shape there.
* `Anim/Track.agda:107` `holdLerp` (6 lines, unused, mentioned by a comment): Track is reworked in Stage 1-2.

### Duplication for the refactor (estimates are lines that could go)
* `pick2` is defined four times with identical clauses: `Anim/Syntax.agda:111`, `Anim/Track.agda:142`,
  `Diagram/Expr.agda:112`, `Diagram/Syntax.agda:124` (and `pick4` at `Diagram/Euclid.agda:118`). A shared
  `Container.Pick` (or a `Fin 2`-indexed constructor `binary : C₁ → … ` in the container libraries) removes
  about 15 lines and a recurring proof obligation (`Expr.Properties.two`, 3 copies at lines 92/97/103).
  Stage 1 (Syntax/Track), Stage 2 (Expr).
* `nth` (list index with default or `Maybe`): `Anim/Nth.agda:34`, `Lower.agda:54`, `Diagram/TextMetrics.agda:33`.
  `member`: `Resources.agda:51`, `Diagram/Names.agda:28`. About 15 lines. Stage 3.
* `Anim/Continuous.agda`: `lift2` (l. ~139) and `Timeline.mergeM` (l. 31) are two partial combinations
  of `Maybe`; `parAt` re-implements `Timeline.merge` pointwise in time; `leafAt` evaluates
  `sampleAt Tr.ℚLerp tr` three times (l. ~116-120, a `where`); `Assembly/Continuous` repeats the
  tick-by-tick induction of `Assembly/Leaf.Over` for the ℚ reading. About 60 lines between them.
  Stage 1 (temporal container: one `Timed` algebra, with discrete ticks as its restriction).
* `Param`/`DParam` (`Diagram/Param.agda:21,39`, `Anim/Param.agda:94-122`, `Anim/DParam.agda:51-81`): two records that
  differ only in the expression language; `nonEmptyParam`/`dnonEmpty`, `instantiate`/`dinstantiate`,
  `mkParam`/`dmkParam`, `paramOf`/`dparamOf` are twins (about 45 lines). `Phases`/`DPhases` are already
  shared through `encodeWith`/`phasesWith`; `Phases.Properties.Over` and
  `DPhases.Properties` instantiate it. Making `Param` a record over the language `E` and `AnyParam`
  a sum would also drop the `AnyParam` wrapper (Backend.Diagram's two renderers). Stage 2.
* `Share`/`SharePhases`/`Formula` (+ `.Properties`, 308+80+190 and 597+340+493 lines): three developments of
  the same shipped-formula story (a formula tree, its shared-node form, the phases of both). The proofs are
  parallel (evalArg/evalOut/evalNode, `*-cong`, `*-ext`). Possibly a few hundred lines of proof could become one
  generic development over a fold (estimate from the parallel structure; not attempted). Stage 2.
* `Place/Properties/Atop.agda:47-80` re-proves `shiftDraw-natural` and `overlay-natural` (31 lines) that
  `Layout/Properties.agda:88-130` proves under the stronger `IsOpsHom`; both need only `h-+`. A topic module
  `Place.Properties.Natural` taking only `h-+` would serve both (and drop the duplicate `private module PS/PT`).
  Stage 2 (diagrams).
* `Anim/Phases.agda:55-73` `withNums` with `headOr`/`tailL` chains; a `Vec`- or `Fin`-indexed
  `nums` would remove the case table and `Phases.Properties`'s `withNums-mapDraw`/`nums-mapDraw` pair
  (estimate, unmeasured). Stage 2.
* `Backend/Reveal.agda:42-55` and `Backend/Plain.agda:41-56` `deckAlg` are the same algebra apart
  from the slide wrapper and the stack handling; the `cong` clause is the long part. One
  `slideAlg wrap-slide wrap-stack` plus the congruence would save about 15 lines. Stage 3 (decks), when the
  deck algebra changes shape.
* `Backend.Diagram` (393 lines): `renderAnimation`/`renderParamAnimation`/`animationWith` repeat
  the `data-*` attribute assembly (l. 227-390); a shared attribute list may shrink it (not examined in detail). Stage 1-2.

### Tests / build
* `make test-browser` (headless Chrome via `check_reveal.py`/`check_plain.py`, 2 x 40 lines) overlaps `test-playwright`
  (`run.mjs`) on the showcase; kept (tests are not weakened). `tests/spike` documents the flipbook-vs-CSS
  spike of `plan/Animations.md` and nothing builds against it.
* Everything.agda omits `Spike`/`Main`/`Driver`, which `make check` then checks one by one (about 40 s measured
  for the nine in a warm tree): each `agda` process re-reads all interfaces. Not changed: the executables need
  `--guardedness`, so they cannot join the aggregate.

## Result

See the final report: lines before/after, `make check` time and RSS, test results.
