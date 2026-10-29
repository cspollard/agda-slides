# Dropped theorems: what the legacy proved and the rebuild does not

Audit of tag `legacy` against branch `rebuild` (tip a2ad981).  Read-only comparison; nothing in
either tree was changed.  Method and honesty notes first, then the counts, the gaps, the
intentional drops.

## Method and confidence
- Inventory: a script (`python3 -I`, top-level and one-indent `name : type` declarations) over every
  `Properties*`, `Laws`, `Natural`, `Valid`, `Container/**` module of both trees: about 790 legacy
  names.  Counts include local helper lemmas, so they are good to a few percent, not exact.
- Matching was by meaning.  Classifications of whole modules from the signature list alone (not the
  proofs) are marked "sig" below; the rest were checked by reading statements and module headers.
  Sample-checked by reading the statements (18): `valid-layout`/`OpOk`, `invalid-rectangle`,
  `footprint-swap`, `names-inst`, `seqAt-boundary`, `win-zero`, `gap-absent`, `par-gap`,
  `par-assoc` (legacy); `Scalar.Hom.digitise` and its `cmd`, `Scene.Tick.tick-hom`/`rel-hom`,
  `Scene.Sample.events-sample`, `Diagram.Natural` header and `layout-natural`, `Diagram.Assoc`
  header, `Backend.Input.Properties`, `Program.Supports` record, and the textual `diff -r` of
  `Container/` in both trees.
- The rebuild documents some of its own omissions (`Diagram/Laws.agda`, `Scene/Laws.agda`
  headers); those are confirmed here.  The swap law was never proved in the legacy (only
  `footprint-swap`, the footprint being invariant under it), so it is a new target, not a regression.
- Classes: KEPT (file unchanged), GEN (replaced by a generic lemma), REST (restated for the new
  objects), INT (dropped on purpose), GAP (a meaningful fact about the new objects with no
  counterpart), OBS (statement about a type or scaffold that no longer exists).

## Counts
| Area (legacy modules) | total | KEPT | GEN | REST | INT | GAP | OBS |
|---|---:|---:|---:|---:|---:|---:|---:|
| Container (`FreeMonad`, `Algebraic`, `Monadic`, `Lowering`, `Sum`, `Interpret`) | 58 | 58 | | | | 0 | |
| Place / layout (`Place/Properties/*`, `Layout/Properties`) | 147 | | | 49 | | 39 | 59 |
| Diagram syntax, names, signature, delta | 55 | | 17 | 30 | 5 | 3 | 0 |
| Ordered scalar, NatQ, faithfulness, discrete | 91 | | 24 | 43 | | 4 | 20 |
| Time and animation (Syntax, Sample, Timeline, Footprint, Continuous, Assembly, Track, Time) | 144 | | 15 | 28 | 7 | 22 | 72 |
| Shipped encodings (Share, SharePhases, Param, Formula, Phases) | 179 | | | | 179 | | |
| Input, steps, labels, machine, lowering of decks | 64 | | 1 | 48 | 11 | 2 | 2 |
| Backends (Common, Plain, Reveal, supports, XML) | 25 | | | 8 | | 8 | 9 |
| Examples (Pairs, PairsHero properties) | 27 | | 5 | 4 | | 16 | 2 |
| **Total** | **790** | **58** | **62** | **210** | **202** | **94** | **164** |

The 94 GAP names collapse to the 14 items below (the Place `Valid` module alone is 26 names).
Container-level: `diff -r` shows every legacy `Container/**` file kept; only `_≈⋆_` moved from
`Lowering/Properties` to `Lowering` (so folds need not import the laws), and `Interpret/Plain`,
`Lowering/Translate` were added.  No container-level law is missing.

## Compact mapping (the twenty that matter most)
| Legacy | Class | Rebuild |
|---|---|---|
| `Signature/foldT-bind`, `Ordered/foldT-bind`, `Gen/toProg-bind` | GEN | `pfold-bind` |
| `foldT-translate`, `MapFusion/fold-translate`, `Assembly/relN-*` | GEN | `pfold-rel-translate`, `pfold-rel` |
| `Ordered/foldT-lower`, `Faithful/faithful`, `Discrete/discrete-is-ordered` | GEN | `pfold-hom`, `Scalar.Hom.digitise` |
| `MapFusion/translate-id`, `translate-∘`, `translate-cong` | GEN | `Container.Lowering.Translate` |
| `Layout/layout-natural` and the `*-natural` family | REST | `Diagram.Natural.layout-natural(-ok)`, `*-nat` |
| `Laws/shiftDraw-∘`, `shift-∘`, `shift-0` | REST | `Diagram.Laws.shiftDraw-shift`, `shift-shift`, `shift-zero` |
| `Laws/∥-assoc`, `═-assoc`, `combine-assoc` | REST | `Diagram.Assoc.besideA-assoc`, `aboveA-assoc`, `layout-*-assoc` |
| `Laws/size-fusion`, `named-size`, `connectP-size` | REST | `Diagram.Laws.size-layout`, `size-named`, `size-connect` |
| `Soundness/soundness`, `names-fusion`, `names-mapDia` | REST | `Names.Soundness.soundness`, `names-fusion`, `Names.usage-mapDia` |
| `Anim/Sample/Properties` agreement of readings | REST | `Scene.Sample.events-sample` |
| `Syntax/Properties/Laws.par-assoc`, `par-comm` | REST | `Scene.Laws.par-assoc-events`, `par-comm-events`, `read-perm` |
| `Assembly/Continuous.assembly` (ℕ frames in ℚ) | REST | `Scene.Digital.digital`, `Scene.Tick.tick-hom` |
| `Assembly/frameAt-assembly` | REST | `Scene.Animation.frame-assembly`, `Scene.Laws.sample-assembly` |
| `NatQ`, `Ordered/ι-*` (ι is an order embedding) | REST | `Scalar.Hom.ι-hom`, `ι-sub`, `ι-hold`; `Model.Rat.ι-+`, `ι-*` |
| `Faithful`: ℕ percentages not preserved | REST | `Hom.ι-pct-fails`, `PctDigital` |
| `Input/Navigation/*` (`prev-next`, `view-next`, `gotoLabel-goto`) | REST | `Program.Navigation` same names |
| `Input/Machine/sem-bind`, `MIso` | REST | `Program.Sem.sem-bind`, `Machine.Bisim` |
| `Input/Supports/*`, `Lower/lowerCmdBody-*` | REST | `Program.Supports.lowerP-*`, `skipU-*`; `Deck.Lower.lowerFlow-++` |
| `Steps/go-bind`, `elab-bind`, `Common/renderBody-bind` | REST | `Deck.Syntax.chunks-++`, `Backend.Render.Properties.render-glue` |
| `Slides/slide-table`, `labelTable-next` | REST | `Deck.Machine.table-deck`, `labelOf-shift`, `labelOf-++` |

## DROPPED-GAP, ranked
Difficulty and priority use the standing rule: identity and composition laws and general
invariants are proved wherever possible.

1. **Valid layouts and the unit laws of the empty diagram** (legacy `Place/Properties/Valid` and
   `Laws`: `valid-*` for every operation, `valid-layout` under `WellSized`, `∥/═/⊙-unitˡʳ`,
   term-level units, `gap-∥`, `gap-═`, `gap-⊙`, `margin-zero`, `nonneg-⊔`, `invalid-rectangle`;
   ~35 names).  Statement: if every sized leaf has non-negative size then every layout has
   non-negative frame, and then `empty` (`spacer 0 0`) is a two-sided unit of `besideA`, `aboveA`,
   `atop`; spacers add; zero margins vanish.  Why it matters: `empty`, `hcat`, `vcat`, `margin`
   are built on it, and `Diagram.Laws` says so itself (units "hold for non-negative sizes only,
   `Space` does not say so").  This is the identity law of the layout monoid structure.
   Difficulty medium (a `Nonneg` predicate, or a `0 ≤` law in `Space`; ℕ gets it free).
   **Priority high.**
2. **Functoriality of scalar maps** (legacy `Layout/mapLayout-∘`, `mapLayout-cong`,
   `MapFusion/mapDia-id`, `mapDia-∘`, `fold-mapDia`).  `mapDia f = translate (mapC f)`, and
   `translate-id`/`translate-∘` exist, but `mapC id ≡ id` and `mapC (g ∘ f) ≡ mapC g ∘ mapC f`
   (shape equality, one clause per `Op`) were never stated, nor `mapLayout id = id`,
   `mapLayout (g ∘ f)`, nor the same for `mapScene`.  These are the identity/composition laws of the
   change-of-scalar functors that `layout-natural` and `tick-hom` are about.  Difficulty easy;
   **priority high.**
3. **Duration and boundary laws of scenes** (legacy `Syntax/Properties/dur-⨾`, `dur-gap`,
   `Time/Properties/seqAt-before/after/boundary`, `Syntax/Laws/par-gap`).  Rebuild has
   `duration-par` and `duration-nonneg` only: no `duration (a ⨾ b) = duration a + duration b`,
   `duration (hold d a) = d`, `duration (delay …)`, `duration (repeat n a) = n · duration a`, no
   statement that the second operand of `⨾` takes over exactly at the boundary from its own time 0,
   and no unit of `Par` (a scene that shows nothing).  Difficulty easy (folds; most by `refl` once
   `Events` is unfolded); priority high (they are the skeleton laws named in Legacy.md).
4. **`atop` commutativity and associativity up to permutation, and layout-level `Par`**
   (legacy `Place/Properties/Commute.atop-comm`, `Laws/⊙-assoc`, `Syntax/Laws/par-comm` at
   layouts).  Rebuild has the sizes (`size-atop-comm`, `size-atop-assoc`) and `par-comm-events`
   but not the frame-and-drawings statement up to `↭`.  Matters because `Par` of scenes lays out
   by `atop`.  Difficulty medium; priority medium.
5. **Periodicity and the remainder under ι** (legacy `Ordered/ι-modBy`, `ι-divBy`,
   `Laws/loop-period`, `Anim/Loop`).  `IsTimeHom` has `h-tick`, `h-floor`, hence `h-hold`, but nothing
   for `Time.rem`; no statement that a looped or repeated scene reads `t mod n` ticks.  `Scene/Laws`
   lists "a tick law for `Repeat` beyond ℕ" as unclaimed.  Difficulty easy for `h-rem`, medium for
   the loop law; priority medium (the page evaluator and `animateBoth` rely on it).
6. **Example-level agreement** (legacy `Pairs/Properties` ×12: ℕ/ℤ/ℚ compile agreement of six
   diagrams, ×4 `Draws` soundness instances; `PairsHero/Properties`: `heroT-correct`,
   `frame-natural`, `pair-natural`, `dot-natural`).  The generic theorems exist (`layout-natural-ok`,
   `soundness`, `digital`, `leaf-ok`) but no example discharges their side conditions (`OkDia`,
   `SidesDia`, `PctDigital`), so nothing shows they are satisfiable on the real deck.
   Difficulty medium; priority medium (acceptance suite value, and a cheap test of the side
   conditions).
7. **Coupling exactness at ticks** (legacy `Continuous/ratioAt-ι`, `inst-exact`, `leaf-tick`,
   `Assembly/Continuous.Exact`, `ex-seg/hold/seq/par/delay`, `NatQ/ι-ratio`; also `piece-start`,
   `progress-0`).  `Hom` gives ι for ticks and scalars but not for `ratio`, `lerp` or `move`: when a
   move's duration divides exactly, its ℚ frame at a whole tick is ι of the ℕ one.  Needed to
   say "interpolated frames digitise" and not only "digital terms digitise".  Difficulty hard
   (exactness predicate on easings); `move-start` and `progress-0` are easy.  Priority medium.
8. **Scene-level footprint and independence** (legacy `Footprint/footprint-⨾`, `footprint-∥`,
   `par-comm-footprint`, `footprint-swap`, `independent-sym`).  `Names.usage` is per diagram;
   a scene has no names fold, so "independent parts commute under `Par`" (which needs gap 4)
   and "a scene declares what its leaves declare" are unstated.  Difficulty medium; priority low
   until gap 4 is taken.  The swap law `(a⨾b)∥(c⨾d) = (a∥c)⨾(b∥d)` under a `Windowed`
   hypothesis was never proved in the legacy either; the rebuild records why it is false without it.
9. **Key-table soundness** (legacy `Binding/on-∈`, `choice-∈`, `bind-kind`, `Reveal/Supports`
   `revealKeys-kind`, `reveal-render`, `reveal-command`, `Plain/Supports` ×3).  The rebuild checks
   `clash-free` by computation only; nothing says a clash-free table decodes each key to the
   command that binds it, or that rendering a command then reading it back is identity.
   Listed under INT in the brief; kept here as a residual because `decode` still exists.  Difficulty easy;
   priority low.
10. **Rendered length** (legacy `Plain/renderDeck-length`, `Reveal/renderDeck-length`): the
    rendered forest has one section per slide.  Rebuild has `renderTalk-++`, `render-index` but
    not the count.  Easy; low.
11. **`animationFinal`** (legacy `Lower/finalFrame-looping`, `finalFrame-no-steps`): the final-frame
    lowering returns the animation's last frame, and leaves a looping one alone.  Rebuild has
    the lowering (`Deck.Lower.animationFinal`) and the fusion laws, not its characterisation.
    Easy; low.
12. **`glue` unit and associativity** (legacy `Steps/bind-assoc`; rebuild has `glue-nil` and
    `chunks-++` but not `glue` as a monoid).  Follows from `chunks-++` on images of `chunks`; only
    needed if `glue` is used elsewhere.  Easy; low.
13. **`win-zero`-style emptiness for `Hold 0`** (legacy `win-zero`, `gap-absent`): covered for decks
    by `hold-out`, not for general scenes.  Folded into gap 3.
14. **Layout/`mapScene` congruence lemmas** (legacy `mapDraw-cong`, `mapAnchor-cong`): folded into gap 2.

Top ten by priority: 1 (high), 2 (high), 3 (high), 4, 5, 6, 7 (medium), 8, 9, 10 (low).

## DROPPED-INTENTIONAL (reasons)
- Shipped encodings `Share`, `Formula`, `Param`, `Phases`, `SharePhases` and their properties
  (179 names): Objects.md "Shipping to the page": ship the event list with parametric leaves and a
  generated evaluator; reintroduce sharing only if page size demands it.
- Frame-list and delta machinery (`Delta/Properties`, `Timeline`, `Nth`, `flipbook`, `length-restsOf`):
  a raw frame list is a scene of one-tick frames; there is no frame-list block (Objects.md, Step 7).
- `Track` and its datatype laws (about 60 helper lemmas, reversal of tracks, easings by cases):
  replaced by Coupling terms; `reverseE`/`reversal` have no counterpart because no reversal
  operation exists (restate if it returns: DROPPED-OBSOLETE, not a regression).
- `LabelC`, `autoLabel`, `Fresh` (`Slides/Properties`): labels are slide data, not commands.
- `Binding` and `Hash` proofs and the `XML/Properties` bridge from `Eq` to `_≈ₓ_`: bindings are
  tables with a computed `clash-free`; the render properties use `≡` on forests (see gap 9).
- Ring-and-setoid scaffolding (`IsLawful`, `_≈ᴸ_`, `_≈ᵖ_`, the cong lemmas, ℤ/ℚ `Ordered` instances,
  `OOps`/`QOps` evaluators, `⊓`): `Space` is ≡-based with a Max and Minus signature (Objects.md).
