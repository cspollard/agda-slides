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
     the fold into `exprOps` (a homomorphism too, `evalWith-subst`). `Slides.Diagram.Layout.Properties`:
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
     - (Proved, `Slides.Anim.Param.Properties`: the frame at tick `k` is the symbolic layout at
       the assignment `i ↦ (parameter of segment i at tick k)`, `discrete-assembly`,
       `paramOf-assembly-canonical`, with the shipped segments identified.)
     - Built: layered signatures (core, sub) and the Euclidean layer, `SegBody.discrete`
       (discrete templates, `Slides.Diagram.Euclid`, `Slides.Anim.DParam`, `DParamCorrect`,
       `DPhases`, `Formula.encD`), tested by `anim-ref` (`dhero`, every tick of the period).
       The point-pair loops are templates (`PairsHero.heroD`, `heroT-correct`) and the Pairs deck
       ships them so: symbolic layout is linear (absolute placement, `Place`/`Overlay`) and the
       formulas of a phase are shared (`Slides.Anim.Share`, `SharePhases`: value numbering into
       a straight-line program, `share-impl`, `unfold-sound`, `pageFrameS-sem`), 18.8 KB for 26
       pairs against 42.7 KB of edits (3 pairs were 779 KB before). Left: simplifying `a + 0`,
       inlining single-use definitions (about 16%), canonical-assignment/`paramOf`-level discrete
       theorems (as `paramOf-assembly-canonical`); `animateBoth` is still always a flipbook
       (its phases are a style, not a template parameter).
     - `toℕ` of `exprOps` is the value at the all-zero assignment (it is not part of
       `IsOpsHom`; layout never applies it).
   - *Continuous time* (built). A template animation ships the tracks (pieces with easings)
     and the symbolic layout; the page evaluates at the real time of each
     `requestAnimationFrame` (`Slides.Anim.Continuous`, `Slides.Diagram.NatQ`/`ExprQ`; players
     in `assets/animation.js`). Size is independent of the tick count. Proved:
     `sampleAt-ι`, `leafAt-ι`, `leaf-tick` (with `Faithful`), `parAt-time`, `seqAt-*`,
     `animAt-dur`, `piece-hold`, `piece-start`. Tested only: the JavaScript (float easings,
     evaluator) against exact `frameAt` at every tick and quarter tick.
     Proved at whole ticks, `Slides.Anim.Assembly.Continuous` (`frameAt-assembly`: the
     continuous frame is the discrete one through `ι` when the segments running at that tick
     satisfy `leaf-tick`'s hypotheses; `atop` needs none, `AtopNatural`) and
     `Slides.Anim.Formula`/`Phases` (shipped formulas and phases mean the symbolic frame).
     Left: `frameAt a τ` for fractional `τ` (the symbolic layout of tick `⌊τ⌋` at each
     segment's sample at `τ - start`, needs floor reasoning on `<ᵗ`); the JSON printing and the
     player's reading of the phases (attribute table, floats) are tested only; a template
     whose differences go negative draws a negative size (no clamping in the page); black-box
     bodies stay discrete.
   - *`Expr` through the generic theory.* `Slides.Diagram.Expr` is already `ExprC ⋆ V`;
     route `evalWith` through `Container.FreeMonad.Algebraic` (`fold-agrees`, as in
     `Slides.Diagram.Syntax.Properties.Generic`), `subst` as `_>>=_`, `rename` as `fmap`, with the monad laws
     from `Container.FreeMonad` (`Eq`, `bind-cong`, `join-assoc`).
   A CSS-transition emitter does not belong here: it adds smoothness, not compression.
3. **Use the generic `Container.*` theory for `Dia`.** Done: `Slides.Diagram.Syntax.Properties.Generic` and
   `Slides.Anim.Syntax.Properties.Generic` show that `fold` and `foldA` are the generic fold
   (`fold-agrees`); `Slides.Diagram.Syntax.Properties.MapFusion` shows `mapDia f` is translation along the
   container morphism `scalarMor f` (identity on positions), hence functorial up to
   equality of programs (`mapDia-id`, `mapDia-∘`) and `fold α (mapDia f d) ≈ fold (pull
   (scalarMor f) α) d` for congruent `α` (`fold-mapDia`). Left: monad laws for
   `Dia`-with-holes if templates are wanted; pulling `Layout` back along a scalar map
   needs the map to be an ordered-ring homomorphism (see `docs/Design.md`).
4. **Laws left over for diagrams** (`Slides.Diagram.Place.Properties.Laws`):
   - Done in `Slides.Diagram.Place.Properties.Valid` (for ℤ and ℚ, via an `IsOrdered` record: the sum keeps
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
8. **Update parsnip** (done). The `parsnip` submodule is bumped from `9ac93f3` to upstream
   `main` (`224299e`: streaming tokenizer fuel, shared lexer, fast `Char` equality, CSS and HTML
   modules). API drift fixed in this repo: the `fixText`, `fixText-valid`, `fromEq` and `both`
   helpers moved from `Data.XML.Sanitize` to `Data.Sanitize` (`Backend.HTML`), and element
   children are indexed by `Pos n` (`Data.Container.Pos`) instead of `Fin n`
   (`Backend.XML.Properties`). `make check`, `make test` (goldens unchanged), `make test-negative`
   and the browser tests pass. Worktrees still need a plain copy of `parsnip/` (the submodule is
   empty in a fresh worktree).
9. **Investigate memory use and time when compiling decks.** Compiling `PairsMain` peaked
   at about 4.4 GB resident in `agda` (typechecking with `--compile`), and a from-scratch
   `make pairs` (no `_build`) took around 20 minutes, much of it GHC compiling the standard
   library's MAlonzo output (`Tactic.RingSolver`, ...). Find out what dominates: which
   modules are heavy to typecheck (profile with `agda --profile=modules` /
   `--profile=definitions`, and `+RTS -s` for the peak), whether large `with`/normalisation
   in the proof modules (`LayoutNatural`, `ParamCorrect`, `Phases`, ...) is pulled into the
   executables, and whether the executables could avoid importing the proof modules at all
   (proofs are erased, but their modules are still loaded and compiled); consider
   `--erasure`, splitting the proof-only modules from the ones the decks import, and a
   documented minimum for RAM and the standard-library version (`v2.3`; an older checkout
   fails with a missing `Data.Bool.ListAction`).
   - *Hot proofs and RTS (perf-hotproofs).* Measured with `--profile=definitions` on a
     clean module, Agda 2.7.0.1. `Slides.Anim.Track.reversal` took 134 s of the module's
     147 s: the `refl`s under `rewrite ... with` made the checker normalise rational
     arithmetic (`1ℚ - 1ℚ`, `1ℚ - 0ℚ`, `gcd`). It now uses `cong` on `if_then_else_` and two
     `abstract` constants (`sub-11`, `sub-10`): 16 ms, module 19 s. `Monadic`
     (`Free⊣Forget-monadic`, 21 s; the whole module 35 s) was investigated but not
     improved: the cost is the conversion check of the `WeakInverse` fields against the
     type `ComparisonF` has (eta-expanding big records; re-elaborating `ComparisonF
     Free⊣Forget` instead of the alias `K` costs 7 s by itself), and four restructurings
     (explicit `comparison-equiv`, copatterns, `T` spelled out, `K` in the signature)
     all gave the same or worse. `PairsScalar` (about 60 s of `_` checks, 2 to 7 s each)
     is not rational `gcd` (the ℤ checks cost as much, 2 to 5 s per diagram): it is the
     layout evaluation itself, linear in diagram size, so only smaller diagrams would
     help; left as is.
   - *RTS flags.* Clean check of `Slides.Examples.Pairs.Properties` (and its 85 s of imports),
     user time and peak RSS, machine loaded (noise about 10%): default 82 to 89 s,
     1.4 GB; `-A64m` 105 s; `-A256m` 90 s, 1.1 GB; `-A1g` 69 to 71 s, 1.5 to 2.2 GB;
     `-A2g` 68 s, 3 GB (swaps); `-A256m -n4m`, `-A256m -c`, `-A256m -G3` no gain;
     `-H4g` 64 to 70 s but 3.9 to 4.8 GB and sometimes swaps. The Makefile now defaults
     `AGDA_RTS ?= +RTS -A1g -RTS` (override with `make check AGDA_RTS=`). A full
     `make check` took 9 min 9 s (was 10 min 34 s; part of that is the `Track` fix).
     A cold `make example talk plain showcase pairs` (Agda plus GHC `-O0`) took 9 min 16 s;
     no GHC flag variants were measured.

   *Status (branch `perf-consolidate`).* Baseline, clean typecheck of every module
   (`--profile=modules`): 634 s, 5.3 GB peak RSS, 30% in GC. Heavy modules: `Anim.Track` 131 s
   (one definition, `reversal`), `Anim.ContinuousAssembly` 111 s, `Anim.Continuous` 67 s,
   `Anim.DPhases` 63 s, `Examples.PairsScalar` 58 s, `Anim.DParamCorrect` 54 s,
   `Anim.ParamCorrect` 30 s, `Container.FreeMonad.Properties.Monadic` 25 s; each module also spends 20-57 s
   "Miscellaneous" loading and re-serialising big interfaces, so time and memory follow how much
   a module imports. Every executable imported 56-59 modules / 10.9-11.7K lines because runtime
   code and proofs shared files. Done, consolidation first:
   - *One proof, two readings.* `Phases`/`DPhases` and `ParamCorrect`/`DParamCorrect` were copies.
     The encoder and grouping are one generic runtime definition (`Phases.encodeWith`,
     `phasesWith`); its meaning is proved once for any reading of formulas
     (`PhasesCorrect.Over`: two facts per slot, `slot-val`, `slot-num`) and instantiated at ℚ and
     ℕ (`PhasesReadings`). `Leaf` is parametrised by the language of its template's numbers and
     the whole assembly induction (leaves-agree, tick-by-tick, numbering, canonical assignment,
     `segmentsOf-nth`) is proved once (`LeafAssembly`); `ParamCorrect` and `DParamCorrect` are
     instances (the discrete one gains the canonical form). `DPhases` went from 261 to 31 lines,
     `DParamCorrect` from 147 to 98; old theorem names are kept as aliases.
   - *Decidable equality by retraction* (`Slides.DecEq`): `Formula`, `Element` (`Delta`), `Draw`,
     Share's `Arg`/`Op1`/`Op2`/`Node` are retracts of sums/products (or of a rose tree, for the
     recursive ones) with one generic equality: about 400 lines of constructor-pair clauses gone.
   - *Runtime separated from proofs:* `Formula`/`FormulaCorrect`, `Share`/`ShareCorrect`,
     `SharePhases`/`SharePhasesCorrect`; `mergeM` moved to `Timeline` (so `Nth` and `Phases` no
     longer import `Continuous`/`ParamCorrect`); `leaf-agrees` moved out of `Param`/`DParam`;
     small shared lemmas in `Anim.Arith`; unused names pruned from `using` lists. Executable
     closures: PairsMain 57 modules / 11,666 lines -> 50 / 7,990; IntroMain 57 / 11,189 -> 50 /
     7,513; ShowcaseMain 57 / 11,105 -> 50 / 7,429; Plain/TalkMain 56 / 10,875 -> 49 / 7,199;
     AnimRefMain 59 / 11,566 -> 56 / 8,855 (it also imports `Continuous`).
   - *Measured* (same machine, under load): clean typecheck 563 s (was 634), peak RSS 5.0 GB
     (was 5.3), GC 167 s. `PhasesReadings` is 20 s where `DPhases` was 63 s; `DParamCorrect`
     0.3 s (the instantiation cost now shows in `ParamCorrect`, 57 s: net -27 s for the pair).
     A cold `make example talk plain showcase pairs animref` (GHC included) took 627 s, agda
     peaking at 1.8 GB resident.
   - *`X.Properties` split* (convention in `docs/Design.md`, "Module conventions"). Every proof
     module was renamed to `X.Properties` (or a topic `X.Properties.<Topic>`), and the mixed modules
     were split: `Track`, `Continuous`, `NatQ`, `Delta`, `Timeline`, `Anim.Syntax`, `Footprint`,
     `Signature`, `Expr`, `Euclid`, `Names`, `Lower`, `Render`, `Backend.Plain`/`Reveal`/`XML`,
     `Share` (the AVL membership modules), `Container.Lowering`/`Interpret`/`Sum`/`FreeMonad`/
     `FreeMonad.Algebraic`; `ExprQ` became `Expr.Properties.Faithful`. `tests/check_closure.py`
     (in `make test`) fails if an executable's closure holds a `.Properties` or `Anim.Assembly`
     module. Executable closures (modules / lines), before -> after: PairsMain 50 / 8,003 -> 50 / 6,997;
     IntroMain 50 / 7,526 -> 50 / 6,458; ShowcaseMain 50 / 7,442 -> 50 / 6,455; Plain/TalkMain
     49 / 7,212 -> 49 / 6,235; AnimRefMain 56 / 8,868 -> 54 / 7,002.
   - *Measured* (same machine): clean typecheck of Everything 197 s, peak RSS 6.25 GB (the same
     tree before the splits but after the renames: 330 s, 5.9 GB; the recorded baseline above was
     358 s, 4.9 GB, so the memory did not drop: more, smaller interfaces are loaded at once). Cold
     compile of PairsMain (`agda --compile`, `-O0`, agda and GHC together, parsnip pre-built):
     276 s, 2.6 GB before -> 108 s, 2.2 GB after; the generated Haskell goes from 605 modules /
     1.10 M lines to 482 / 0.58 M.
   Remaining: `Anim.Track` (`reversal`) and `Examples.Pairs.Properties` belong to the hot-proofs work;
   `ContinuousAssembly` (107 s) and `Continuous` (67 s) are now outside every deck executable
   except `animref`, and could be sped up by explicit signatures / `abstract` for the big `with`
   proofs; the categorical objects of `Container.*` (`Free₀`, `Alg`, `Poly`) keep their proofs because they are
   the definitions; `Slides.Spike.Reveal` is kept (documented in `docs/Design.md`,
   target `make spike`). `--erasure` was not tried. Peak memory is still set by the single
   `make check` process; the lever is fewer, smaller interfaces per module.
10. **Unify more of the core ideas.** Diagrams, animations and slides are each built the same
    way (a free monad over a container, interpreted by an algebra), yet they are separate
    languages with separate backends. Investigate whether they can be one language, or one
    family sharing structure: a slide as a diagram whose leaves are text, images and nested
    diagrams; an animation as a diagram over a time-indexed scalar (`Anim S T` as `Dia` over
    `ℚ → …`, so a still diagram is the constant animation); a deck as an animation over slide
    indices (sequence of slides is `Seq`, simultaneous elements are `Par`). Questions to settle
    first: which containers are really the same (`Seq`/`Par` against `Beside`/`Above`/`Atop`);
    whether one layout algebra can serve all three, so that `layout-natural`, the assembly proofs
    and the delta/phases encoding are proved once; what the backends (`Reveal`, `Plain`, the
    JS player) lose or gain; and the cost to compile time. Aim to remove code and duplicated
    proofs, not to add a layer; keep the existing theorems as corollaries. The staged plan, with
    pros and cons and the functional-reactive reading, is in `plan/Unify.md`.

## Risks

- **Submodule.** parsnip is pinned by the submodule commit; builds need
  `git submodule update --init`.
- **Library drift.** The README records the agda-categories commit and Agda version
  used (`c2e7c13e`, 2.7.0.1).
- **Typechecking time.** `make check` is about 90 s; keep instance search out of the
  core (see "No instance search" in `docs/Design.md`).
