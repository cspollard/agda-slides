# Stage 2 spike: one temporal container for the animation proofs

Branch `stage2-assembly` (modules `src/Slides/Spike/Stage2/*`, all `--safe --without-K`, no
postulates, no holes, no instance search in core; theory modules only).  Measured with
Agda 2.7.0.1, `+RTS -A1g`, `/usr/bin/time -l`, imports cached (a bare module that only loads
the library costs about 3.9 s, 1.7 GB, so subtract that).  Read with `docs/Time.md`.

## 1. Design chosen

* `TimeC = Seq, Par | Hold n, Delay n, Repeat n | Drive tr`, `SceneC S = TimeC ⊎ DiagramC S`,
  `Scene S = SceneC S ⋆ ⊥` (`Scene.agda`, 67 code lines).  `Repeat` and `Drive` are new.
* A segment is a derived form: `segS (tr, d) = Hold (dur tr) (Drive tr (inj d))`.  `inj` is the
  diagram as an eternal scene (duration 0), `Drive tr` binds the template's one variable to the
  track's value at local time (substitution along a signal, plan 2.2; the carrier is a reader
  `ℚ → X`, `Drive` is its `bind`), `Hold` gives the window and the duration.  `Seg` is not needed.
* Carrier `TM A = ℕ × (ℚ → Maybe A)` as in Stage 0.  `Seq` is guarded: `seqW x y = holdT (|x|+|y|)
  (seqAt x y)`.  `Par` is `parAt` with absence as unit.  `copairAlg` is the Set-level copairing.
* `embed : TAnim → Scene (Expr ⊤)` for template-only animations (`TAnim = AnimC ⋆ (Track ℚ × Dia
  (Expr ⊤))`, `toAnim` maps into the existing `Anim`).  blackBox and discrete segments are not
  embedded (see 5).

## 2. What was proved (files, code lines)

| name | file | what |
|---|---|---|
| `embed-dur` | Scene/Properties | duration of the scene is `Anim.dur` |
| `inj-cst`, `fold-algD`, `segS-sample` | Scene/Properties | `inj d` is constant in any extensional algebra (14 clauses); a segment's frames are the existing `leafAt` (pointwise, no funext) |
| `lifting-lemma′` (`Lift′.lift-natural′`) | Lift (42) | Stage 0 lemma plus `seqW`, `Repeat`, `Drive`; Φ-naturality along any algebra homomorphism |
| `layout-at′`, `names-at` | Instances (25) | instances; each costs one extensionality proof (14 clauses) and one line |
| `footprint-embed` | Footprint (20) | the static instance: `cata` into `Usage`; equals `Anim.Footprint.footprint` |
| `RelN`, `relN-seq`, `relN-par`, `assembly`, `frameAt-assembly′` | Assembly (116) | the assembly, see 3 |
| `embed-agree`, `animAt-toAnim`, `frameAt-assembly-new` | OldNew (69), Old (9) | the embedding's frames equal `animAt`'s at whole ticks, so the new theorem IS the old statement for `frameAt (toAnim t)` |
| (a) to (e) | Decisions (66) | see 4 |

## 3. frameAt-assembly: old against new (honest)

Old statement (`Assembly.Continuous.frameAt-assembly`, hypothesis `Good a k`, local to the tick).
New (`Assembly.frameAt-assembly′`, `Old.frameAt-assembly-new`): same conclusion, hypothesis
`AllExactT` (global: every leaf exact at each of its own ticks), which is the old
`frameAt-assembly-all`.  **The local `Good` form was not re-derived** (it needs the old `Seq`
arithmetic; no other module uses it).

| | old | new |
|---|---|---|
| the theorem module | 111 code / 230 total lines | 116 code / 226 total |
| plus supporting definitions and lemmas | `Continuous` defs (animAt, segAt, lift2, ~35), `lift2-just`, `animAt-dur`, `segAt-dur` (~23) | `Scene` (67), `Scene.Properties` needed parts (~85: inj-cst 25, algD-ext 14, rescale-ext 14, tick lemmas 25, ...) |
| check time (module alone) | 44.6 s user, 6.9 GB | Scene.Properties 6.4 s + Assembly 5.7 s, 1.8 GB each (minus 3.9 s load each) |

**The assembly proof does not shrink** (116 against 111 code lines).  What disappeared: the
`Maybe`/`lift2` plumbing, `Good` and its arithmetic.  What appeared: the tick calculus
(`nth-++g`, `relN-seq`, `relN-par`, 30 lines) and, outside the theorem, the cost of defining
segments as `Hold (Drive (inj d))` (about 60 lines: `inj-cst`, `algD-ext`, `rescale-ext`,
because the reader carrier makes equality of children an equality of functions).  Net on
main, for this theorem plus its definitions: roughly equal (old about 170, new about 190 before
deleting the bridging modules, all of OldNew/Old (78) disappear on migration, giving about
110 to 130 new against 170 old: a saving of 40 to 60, not the plan's "three proofs become one
instance").  The 7x compile-time gain is mostly proof style (guards stated at an abstract
boolean, `subst₂` instead of `rewrite` on `ι k`, which normalises large rationals); the old
file could be restyled the same way, so it is not evidence for the design.

The lifting lemma is **not** what makes the assembly work.  It relates two algebras at the same
(ℚ) time; assembly relates the ℚ clock to the ℕ tick clock.  What carries it is a logical
relation over the temporal skeleton, `RelN R` (duration equal, `R` tick by tick), closed under
`seqW`/`++` and `parAt`/`merge`, with the leaf supplying `leaf-tick`/`Faithful`.  Spatial
operations above a leaf would still need `Faithful` (only `atop` is unconditional, `atop-ι`).

Discrete assembly (`Param.Properties.discrete-assembly`, `Assembly.Over`) and the leaf assembly
(`Assembly.Leaf`): **sketched, not proved.**  `Over`'s `Agree` is `RelN` with a tick offset `t`
and a family `R k = Rel (G k)`; `Agree-++`/`Agree-merge` are `relN-seq`/`relN-par` plus
weakening, and `Agree-length` (about 25 lines) disappears because `RelN` carries the
duration (the leaf supplies `frames-length`).  Estimated saving in `Over`: 20 to 30 of 67 code
lines.  `Leaf` (216 code): about 90 lines are that induction (shrinks by about half); about 125 are
the variable numbering (`numbered`, `assignAt`, `canonical-good`, `segmentsOf-nth`), which is a
fresh-variable supply and is untouched (it is `Drive` giving each node a variable: a later
instance, not a deletion).

## 4. The decisions

(a) **Presence window.**  Every primitive under `Hold`, durations in `ℕ`.  Evidence:
`seqAt-leak` (a bare eternal left operand shows only before time 0 and is lost at every
time ≥ 0), `seqW-bare` (with the guard a bare primitive in a `Seq` shows nothing: the
window `[0,0)` is empty).  `ℕ∞` is rejected: the list reading (`timeline`, `length-dur`,
`nth`) and `Footprint/Render/Phases` need finite durations, an eternal value has no
list, and every `ι n` in `seqAt` would need conatural arithmetic.  Cost of `Hold` in the lemma:
`hold-nat`, 3 lines, already in Stage 0.

(b) **Seq window guard.**  `seqAt` at `τ < 0` shows the left operand at a negative argument; at
`τ ≥ |x|` it shows `g (τ - |x|)` including past `|y|` (`seqAt-leak`).  For windowed operands
(everything under `Hold`) both are `nothing`.  Minimal fix: `seqW`, a `holdT (|x|+|y|)` around
`seqAt`.  It is windowed by construction (`seqW-out`), keeps the lifting lemma
(`seqW-nat` is `hold-nat` of `seq-nat`), and agrees with `seqAt` at whole ticks on windowed
operands (`seq-agree`).  The all-τ agreement needs ℚ order lemmas; **not proved** (not needed
for the existing readings, which are whole ticks).

(c) **Set-level copairing.**  `copair` on setoid `Func`s does not suffice for plain `cata`: it
needs a `cong` per summand, and a Set-level algebra is a `Func` only if it is extensional
(no funext), which is exactly the `*-ext` proof.  Add the 3-line `copairAlg`
(`Scene.agda`); `copair-forget` proves `copair` is `copairAlg` of the forgotten algebras.
Extensionality then enters only where a lemma needs it (14 clauses per diagram algebra: layout,
names, the reader algebra).

(d) **Repeat.**  `Repeat n` has one child; `loopT` is n guarded `Seq`s.  Proved: `loop-dur`
(`n * |x|`), `loop-tick` (at whole ticks, `x` at the tick modulo `|x|` for the first
`n*|x|` ticks, nothing after), `repeat-phase` (`Steps`' `both`: the tick `i + φ*n`
shows `x` at `i`, from `Loop.index<`, `index-step`).  `Loop.phase`, `phase-id`, `phase-period`
are the same law for infinite repetition (mod).  `Phases`' lists of phases per tick would be
`sample` read on the ℕ clock; not done.

(e) **Padding.**  `par` pads with `none` (a present spacer) only to equalise durations (swap
law).  Absence is a unit of `Par` on the nose (`mergeM-gap`), the present empty frame only up to
layout equivalence (`none-not-unit`: not equal as diagrams; `Place.Properties.Laws.⊙-unitˡ`
for valid layouts).  An absent gap is `Delay k (Hold 0 _)` (`gap-delay`), so `none` can go and
`Delay` is the padding.  `delay-tick` gives `Delay` on whole ticks.  The swap law itself
(equal-duration `Par` of `Seq`s on `TM`) was not re-proved.

## 5. What each existing module becomes

* `Anim.Syntax`: `AnimC`, `foldA`, `dur`, `hold/tween*` stay until the migration is done;
  `Seg`, `blackBox`, `discrete` removed last (discrete bodies need an ℕ-clock Drive, see layers).
* `Anim.Continuous`: `animAt`, `segAt`, `leafAt`, `lift2`, `frameAt` deleted (replaced by
  `sample` and `framesD`); `seqAt`, `parAt`, `sampleAt`, `Timed` move into `Scene`.
* `Continuous.Properties`: `lift2-just`, `animAt-dur`, `segAt-dur` deleted; tick lemmas kept.
* `Assembly.Continuous`: replaced by `Assembly` (this spike), global hypothesis.
* `Assembly` (Over): shrinks to the calculus plus the symbolic `Rel` (estimate).
* `Assembly.Leaf`: induction part shrinks, numbering part unchanged.
* `Timeline`, `Footprint`: `Footprint` becomes `usage` (20 lines, `footprint-embed`);
  `timeline` stays as the ℕ-clock reading (it is `tickQ`'s target).
* `Loop`: becomes corollaries of `loop-tick`.  `Param`, `Phases`, `Share`, `Render`: untouched.

## 6. Time-domain layers used (docs/Time.md §4)

* **Core** (`+`, `⊔`, literals, order): durations `ℕ`, `ι-+`, `ι-⊔`, `atop-ι`: unconditional.
* **Sub**: `ι-∸` is used only under `n ≤ k` (the exact case: `seqAt-tick`, `delay-tick`); the
  ℕ side's monus `k ∸ n` is only ever applied under that guard, so no `Faithful` is needed for
  the temporal skeleton.  `Faithful` appears only in `leaf` (template sizes).
* **Ord** (`<ᵇ`, `≤ᵇ`, `<ᵗ`): all windows and guards; `ι-<ᵗ`, `zero≤ι` (unconditional).
* **Floor** (`%`): `Repeat` on the ℕ clock (`loop-tick`); the ℚ-clock `Repeat` was not stated
  (it would need ℚ floor, `Floor` layer in ℚ).
* **Scale / Ease**: inside the `Track` payload of `Drive` (`sampleAt`, unchanged: `Scale` is
  `τ/d`, `Ease` the piece's progress); the lemmas never look inside, they use `sampleAt-ι`.
* Semantics is ℚ (`TM`), observation is the ℕ clock `tickQ` along `ι`: the §3 principle.  The
  tick clock is a *reading* of the ℚ scene (`RelN` relates `tickQ` of the ℚ sample to a list), not a
  second language; the discrete `Euclid`/`DExpr` templates are the one place where an ℕ
  evaluation (`units`, floor, then `fromℕ`) differs from evaluating in ℚ, and they are not
  embedded.  A discrete segment would be `Drive` whose parameter is `units ∘ track` with the
  scalar read in `natOps` (a different reader carrier, `ℕ → Layout ℕ`).

## 7. Instantiation cost, risks

Measured (module alone, over the 3.9 s library load): `Lift` 0.2 s, `Instances` (layout, names:
the lemma applied at both) 0.0 to 0.1 s, `Footprint` 0.3 s, `Scene` 0.0 s.  The generic lemma
is cheap to instantiate; its cost is the 14-clause extensionality proof per algebra, which is
the real price of `--without-K` without funext.  Not measured: instances at the symbolic
`Layout (Expr ℕ)` (Phases) and at the discrete reader carrier.
Risks: (1) the reader carrier makes children equalities function equalities (the 60 lines);
a leaf-parameterised variant (`Scene S L` with a leaf semantics and a naturality hypothesis, as
the old `AnimC ⋆ Seg`) avoids `inj-cst`, `algD-ext`, `segS-at` and is the cheaper alternative if
"segment as derived form" is not valued; (2) `Good` (local) lost; (3) all-τ agreement of
`seqW` with `seqAt` unproved; (4) discrete bodies and Phases/Leaf not ported; (5) estimates of
savings for `Over`/`Leaf` are estimates.

## 8. Migration order, gates

1. Add `Scene`, `copairAlg`, `Lift`, instances beside the old code (no deletion); gate: `make
   check`, closure check, same goldens.
2. Port `frameAt` to `framesD`; prove `embed-agree`; gate: `AnimRef` test unchanged.
3. Replace `Assembly.Continuous` by `Assembly`; delete `lift2-just` etc.; gate: line count down,
   check time not up.
4. Port `Over` to the calculus (`RelN` with offset); gate: `discrete-assembly` unchanged
   statement.
5. `Repeat` replaces `Loop`; `none` replaced by gaps; gate: Phases/Share tests.
6. Only then consider `Seg` removal and discrete bodies.

## 9. Recommendation: conditional GO, on a reduced scope

GO for steps 1 to 5: the container, the Set-level copairing, the lifting lemma with
`Seq` guard, `Repeat`, and the shared tick calculus.  It is cheap to compile, the instances are
nearly free, `Repeat`/`Loop`/`both` and the padding question are settled with proofs, and the
temporal skeleton needs no `Faithful`.  **NO-GO on the plan's headline claim**: the continuous
assembly proof does not shrink, expected net saving is about 40 to 60 lines for it and about
30 to 60 more across `Over`/`Leaf`, out of roughly 1100 code lines in `Anim.Assembly*` and
`Continuous*`; the numbering half of `Leaf` and `Phases` are unaffected.  The recommendation
becomes NO-GO if the migration of `Over` shows no saving (step 4 gate), or if the discrete reader
carrier needs a second 60 lines of the same kind.  It becomes a firm GO if the leaf-parameterised
variant (7, risk 1) is adopted (about 60 fewer lines) and `Over`'s saving is confirmed.

## Plan corrections for `plan/Unify.md`

* Stage 2's "three assembly proofs become instances of the lifting lemma" is wrong: the lemma is
  same-clock naturality; assembly needs a ℚ-to-ℕ-clock relation (`RelN`).
* "Durations in `ℕ∞`" is not needed: `Hold` over `ℕ`.
* `Drive` (time-varying parameter) was missing from `TimeC`; `Seq` needs the window guard.
* `Container.Sum.copair` does not suffice; add `copairAlg`.
