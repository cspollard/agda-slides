# The switch to parametric time, steps 1 and 2 (branch `time-switch`)

What landed, what moved, what is not proved, and what this changes in `docs/Time.md`,
`docs/Stage2.md` and `plan/Unify.md` (not edited).  Read with `docs/Time.md` section 7.

## 1. The Clock record (`Slides.Time`)

`Clock` is the explicit model record of the layered time theory: a time domain `T`, its scalar layers
as the *existing* record `OOps T` (core `0 + ⊔ fromℕ`, sub, Ord, Floor; not repeated), the boolean
order `_<ᵇ_`, and `ι = fromℕ`.  `ClockLaws K` (a separate record, so what executables read carries no
proofs) has the select is the order (`lt-spec`) and the homomorphism laws the proofs use: `ι-0`, `ι-+`,
`ι-<ᵇ` (unconditional), `ι-∸` (guarded `b ≤ a`).  Instances: ℚ (`Slides.Time.Rat`, from `ratO`,
`_<ᵇℚ_`, no computation in ℚ: laws are `NatQ.Properties`/`Ordered.Properties`) and ℕ
(`Slides.Time.Nat`, every law `refl`).  `ι : ℕ → ℚ` is the homomorphism between the two models.
`Sem K` is the temporal skeleton (`Timed`, `seqAt`, `parAt`); its laws (`seqAt-before/after/boundary`,
`parAt-*`) are in `Slides.Time.Properties` against any clock, and `Continuous.Properties` lost its ℚ
copies.  `QLaws` (floor/min specs) stay a separate record: the skeleton does not use them.
Not in the record, deliberately: `+-assoc`, `+-minus`, `nlt`, non-negativity (Stage 4's `nested-at`
needs them; nothing here does), density/induction (named hypotheses), `Scale`/`Ease` (ℚ only; see 3).

## 2. One temporal container (`Slides.Anim.Syntax`, `Sample`)

`TimeC = Seq | Par | Hold n | Delay n | Repeat n | Drive tr`; `Scene A = TimeC ⋆ A`;
`Anim = Scene Tmpl` (leaves are templates `Dia (OExpr ⊤)`, eternal until a `Hold`).  Deviation from the
Stage 2 spike, as its risk (1) recommended: the diagram operations are *not* in the scene signature
(the leaf is a whole template, `Scene A = TimeC ⋆ A` as in Stage 4), so `inj`, `algD-ext`,
`rescale-ext` and `inj-cst` (about 60 lines) do not exist.  `seg tr d = Hold (dur tr) (Drive tr (pure d))`
is a derived form; `Seg`, `SegBody`, `blackBox`, `none`, `pad`, `par O` are gone.  `hold n d` embeds a
`Dia ℕ` by `lit`.  A gap is `delay k (hold′ 0 _)` (`gap`).
`Sample` reads a scene in *any* clock: `TM X = ℕ × (T → Maybe X)`, `seqW` (windowed), `parAt`, `holdT`,
`delayT`, `loopT`, `driveT`; the frame carrier is the reader `T → Dia T` (`Drive` is its bind), a leaf is
`inst p d = mapDia (evalO O (λ _ → p)) d` in the clock's own scalar.  The only clock-specific datum is how
a track is read at a time (`val`): `ratVal` (`Continuous`) and `natVal = units ∘ sample` (`Timeline`).
`timeline a` (ℕ clock) is the tabulation of `framesN a`; a tick with nothing shown is the empty frame.
`foldS` is the local fold; `Syntax.Properties.Generic` links it to the generic algebra theory
(`Congruent`, one clause, `foldS-bind`).

## 3. Assembly (`Slides.Anim.Assembly`)

`Assembly.Calculus K₁ K₂` is `RelN R x y` (durations equal; `R k` relates `x` at `ι₁ k` to `y` at
`ι₂ k`, `R` a family over the tick) with `relN-hold/seq/delay/par/mono`, using only `ClockLaws` (window
and order matched by `ι`, exact subtraction).  Two instances, each one case per connective:
* `Assembly.Continuous` (ℚ against ℕ): `AllExact a ⇒ RelN _ (readA ratClock ratVal a) (readA natClock natVal a)`,
  `frameAt-assembly`; `Faithful` is used in the segment case only (`inst-exact`).
* `Param.Properties` (ℕ against ℕ): `induct`, the symbolic scene `place` is the same skeleton read over
  the free scalar; `assembly`, `assembly-canonical`, `paramOf-assembly(-canonical)`.
`Assembly.Leaf` is deleted: the numbering half became `Numbered`/`assignAt` over the *list* of leaves
(`place` returns it), which is about 60 lines instead of about 180 over a tree.  `Over` lost `Agree`,
`Agree-++`, `Agree-merge`, `Agree-length` (the calculus carries the duration) and `Nth` lost
`nth-merge`, `nth-frames`, `nth-replicate`.

## 4. Old theorem to new

| old | new |
|---|---|
| `seqAt-before/after/boundary`, `parAt-time/dur` (ℚ) | `Time.Properties` at any clock; ℚ is a corollary |
| `animAt-dur`, `segAt-dur`, `lift2-just` | `Sample.Properties.sample-dur`, `frames-dur` (no `Maybe` plumbing) |
| `leafAt-ι`, `leaf-tick` | `framesQ-seg-ι`, `inst-exact`, `leaf-tick` (same statement) |
| `Assembly.Continuous.assembly`, `frameAt-assembly-all` | `assembly`, `frameAt-assembly` (hypothesis `AllExact`) |
| `frameAt-assembly` with local `Good a k` | **moved**: not re-derived (as `docs/Stage2.md` said); no module used it; `RelN` is over all ticks |
| `Over.Agree*`, `leaves-agree`, `Assembly.Leaf.assembly` | `induct`, `Param.Properties.assembly` |
| `leaves-numbered`, `canonical-good`, `segmentsOf-nth`, `InTree` | `place-numbered`, `canonical-good`, `segmentsOf-nth` over lists |
| `paramOf-assembly(-canonical)` | same names; leaves are a list; the second component says `nth ls d ≡ just lf ⇒ idx lf ≡ d × shipped segment d` |
| `length-dur`, `timeline-⨾` (refl before) | `Timeline.Properties` (`timeline-⨾` proved: `applyUpTo` split) |
| `merge-assoc`, `merge-comm`, `par-comm` | `par-assoc`, `par-comm` pointwise in time (`Syntax.Properties.Laws`, `Commute.mergeM-comm`) |
| `merge-swap`, `timeline-swap` | **not re-proved** (equal-duration `Par` of `Seq`s needs window arithmetic; as Stage 2) |
| `pad`, `par` laws, `par-layout`, `timeline-none/pad` | **gone**: absence is the unit of `Par` on the nose (`par-gap`), `par` is `∥ᵃ` |
| `footprint-none/pad/par` | gone with padding; `names-inst`, `names-discrete`, swap, comm, symmetry kept |
| `dur-pad`, `par-balanced`, `dur-par` | gone; `dur-seg`, `dur-gap`, `dur-flipbook` |
| `foldA-bind` | `foldS-bind` (setoid form, `Congruent`) |
| `Slides.Anim.Loop` | untouched (about `%`, independent of `Anim`); `Repeat`'s tick reading (`loop-tick`, Stage 2 (d)) is **not stated** here, only its duration (`sample-dur`) |

## 5. Decks and shipped data

* `blackBox` dropped.  Function-bodied animations (`marching`, `grow`, `hero`, `longF`, `wholeF`) are now
  `flipTween`/`flipTrack`: a flipbook is a lowering target (`flipbook`: one `hold 1` per frame), not syntax.
  Frames identical.  Other deck edits: `parI a b` and `a ∥ᵃ b` (no `natOps`, no `par`), `timeline a`.
* A flipbook has constant tracks, so `paramOf` ships a parametric encoding only if some track *moves*
  (`moving`): otherwise nothing would change (not a new feature: the old `blackBox` also made `paramOf` fail).
  This keeps every golden byte-identical.
* `Anim ℕ (Seg ℕ)` is now `Anim`.

## 6. Measurements (same machine, both cold, `make check`, `/usr/bin/time -l`)

main 267 s, 4.94 GB peak; `time-switch` 256 s, 4.36 GB (-4% time, -12% memory).  The 350 s / 6.6 GB
figure of `docs/Map.md` was a different run; the comparison above is paired.  Source: -40 lines
(1556 insertions, 1596 deletions in `src/`), -55 non-comment non-import code lines (10046 to 9991) with
`Slides.Time*` (88) added; the assembly group (Assembly, Assembly.Continuous, Assembly.Leaf,
Param.Properties) 486 to 443 code lines, so the "250 new lines" gate is not approached.

## 7. Corrections

* `docs/Time.md` section 4: the model record does not need `Scale` to *state* the skeleton; `Scale`/`Ease`
  enter only through `val` (how a track is read), the one clock-specific datum.  Section 7b question 1 is
  answered: `Clock` is a parameter of `Sample`, `Assembly` and the skeleton laws, and ℕ is a model of it,
  so the tick reading is the same algebra at the clock ℕ, not a second language (`Timeline` is a tabulation).
* `docs/Stage2.md`: (a) the leaf-parameterised variant removes the 60-line `inj-cst` family; (b) the
  assembly proof does shrink once the relation is generic over two clocks (`RelN`) and `Over` loses `Agree`:
  the old assembly group (Assembly, Assembly.Continuous, Assembly.Leaf, Param.Properties) was 486 code lines
  and is 443, and the new group adds the first clock-generic statement; (c) `RelN` is not ℚ-versus-ℕ
  specific: Param (ℕ against ℕ) is the same calculus; (d) decision (b): `seqW` agrees with `seqAt` at whole
  ticks, used here through `win-ι`; the all-τ agreement is still unproved.
* `plan/Unify.md` (4c, 4d): `Hold n (Drive tr (pure d))` with the diagram leaf (not `inj`) is the segment;
  the ℕ reading is `Sample` at the clock ℕ with `val = natVal`, not a separate reader carrier
  (Stage 2 risk (4): the second 60 lines did not appear); `copairAlg` was not needed (no diagram
  operations in the signature).

## 8. Not proved / not done

* swap law (`(a ⨾ b) ∥ (c ⨾ d) = (a ∥ c) ⨾ (b ∥ d)` for `dur a = dur c`): it is **false** as stated now,
  because leaves are eternal: it needs the operands *windowed* (`fb τ = nothing` outside `[0, |b|)`), which
  holds of everything under a `Hold` and of every `Seq`; a `Windowed` predicate on `Anim` plus window
  arithmetic is the proof, not written;
* `Repeat`'s tick law; all-τ agreement of `seqW`/`seqAt`; fractional-time assembly (browser-tested);
  `AllExact`/`place` support only `Seq`/`Par`/`Delay`/`Hold`/segments (`Repeat`, a bare `Drive`, a free leaf
  have no parametric encoding and no assembly statement).
* Stage 4 (deck embedding, `Body⁺`/`Prog` collapse) not started.
