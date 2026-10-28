# Stage 4 spike: is "a deck is a scene" coherent?

Sections 1-5 are the spike (branch `stage4-spike`); sections 6-8 are what landed (branch `deck-scene`) and
what it corrected in 1-5.

Branch `stage4-spike`; code in `src/Slides/Spike/Stage4/` (`Clock`, `QClock`, `Embed`,
`Collapse`; 316 lines, `--safe --without-K`, no postulates or holes, no instance search; each
module checks in about 1 s over its imports, 4.5 s with the library loaded).

## 1. The clocks, and "nested by substitution"

Signature `TimeC` (Seq, Par binary; Delay n unary), `Scene A = TimeC ⋆ A` (leaves `A`).  Three
clocks, all the same carrier `TM X = ℕ × (T → Maybe X)`:

* animation clock: `τ : T` (ℚ), local to a leaf;
* step clock: ticks `ℕ`, read in `T` through `ι : ℕ → T`; a slide body is a scene whose `Delay 1`
  nodes are the `pause`/fragment boundaries (`Embed.toScene`);
* deck clock: ticks of the same kind; a deck is `Deck A = Scene (Scene A)`, a scene whose leaves
  are slides.  `Seq` of slides is a `Seq` node whose children are `pure slide`.

There is ONE clock theory (`Clock`: `T`, `+`, `-`, `<ᵇ`, `ι`, with assoc, `ι` additive, `(a+b)-a = b`,
`a+b ≮ a` for nonneg `b`, nonneg `ι n`); "coarser clock" means the same ordered monoid read at a
coarser tick, not another type.  Nesting is substitution of the free monad:

    join d = d >>= id                      -- Scene (Scene A) → Scene A, flattening
    nested-flat : sample ℓ (t >>= f) ≈ sample (λ a → sample ℓ (f a)) t       (proved)

i.e. sampling is the Kleisli-extension of the leaf semantics `ℓ : A → TM X` along the monad
`TimeC ⋆ –`: `sample ℓ ∘ (>>= f) = sample (sample ℓ ∘ f)`, the `foldT-bind` law.  The clock
substitution is the shifts already inside the algebra (`Seq` evaluates its right child at
`τ - ι n`, `Delay` likewise); no extra clock-transform operation is needed.  Clock composition is
the monoid action of ℕ on T, `at k τ = ι k + τ`, with `at k (at j τ) = at (k+j) τ` (`at-compose`).

## 2. The lemma (Clock.agda, about 55 proof lines; against the abstract `Clock`, then at ℚ)

`nested-at`: for slides `p s` and leaf semantics `ℓ`, with `d = |p|` the duration of `p`, the deck
`Seq p s` sampled at (deck step `d`, slide step `j`, animation time `τ ≥ 0`), that is at
`at (d + j) τ`, equals the slide `s` sampled at `at j τ`.  `nested-at-flat` is the same for
`join` of the deck (the flat scene).  Proof: `at-compose`, `seq-right` (uses `a+b ≮ a`,
`(a+b)-a = b`).  `QClock` instantiates the record at ℚ (`ι` from `NatQ`, additivity and `≤ᵇ`
from `NatQ.Properties`, rest from `ℚP`) in 56 lines, no computation in ℚ.  `Clock.Sem` is
stated for any model, so a second `T` needs only the record.

## 3. Coherence with today's decks

* `Embed.toScene : Prog (Nav ⊎ C) ⊤ → Scene (Maybe V)`: `show v ↦ Par (leaf v) rest`,
  `await next ↦ Delay 1 rest`, other awaited commands and labels are control and vanish.
  `dur-toScene`: the duration is the number of `next` awaits (proved, 18 lines).  This is
  exactly `Steps`: everything after a pause is present from a later step.  NOT proved: the
  frame agreement with `Steps.steps` (the `fragment` wrapping) and the sample at step j showing
  the first j+1 chunks; the statement is short (a `Par`/`Delay` induction) but unwritten.
* `ContentC`/`LayoutC` stratification is untouched: leaves `V` (here the scene vocabulary of
  `Prog`) stay carrier-specific; only the temporal skeleton is shared.  The leaf type is a
  parameter of every statement, which is what the plan asked for.
* Body⁺ and Prog: `Collapse.goBy` is `Steps.Input.goBy` with the same five clauses on
  `Prog X _` over `Shape BlockC`; it typechecks unchanged (positions are literally ⊤, shapes
  reduce to the same sums).  So the duplication is only the name: `toProgC`/`toProg` and one of
  `lowerCmdBody`/`lowerDeck` can go.  Not done (changes main): retargeting `elabL` and the
  `Steps.Properties` statements, then checking `Lower.Properties`.

## 4. Verdict

GO for Stage 4 as a *temporal-layer unification* (decks = scenes with slide leaves): the
substitution law is cheap and independent of the time model.  Cost of the lemma: 166 lines in
Clock including the model record and `alg-cong` (the 3-case congruence is most of the proof;
`nested-flat` itself is 3 lines), 56 for ℚ.

Unproved or open:
* `Hold`, `Repeat`, `Drive` not in this spike's signature (Hold is a pointwise guard needing
  `0 ≤ τ`; Repeat is iterated Seq; Drive substitutes values, not clocks): the `alg-cong` clauses
  are the same shape, expected one line each, not written.  Stage 2's guarded `seqW` would add
  the window guard to `seq-right` (needs `Nonneg τ`, already a hypothesis).
* `nested-at` is a pointwise sampling law at the start of a slide with a prefix of known
  duration; a general "slide k of an n-slide deck" needs a fold over the deck, not written.
* Navigation (goto, prev) is not time: a deck's clock is linear; the control machine
  (`Input.Machine`) selects the tick, so jumps are state, not scene structure.  The scene says
  what is shown at tick k; the program order is what `Prog (Nav ⊎ C)` quotients.  The spike
  does not connect `toScene` to the machine's reachable states.
* The animation clock inside a step is the leaf's own `T → Maybe X`; there is no ℕ-to-ℚ
  `Faithful` issue because durations stay in ℕ and shifts are by `ι n`.

Estimates (rough; not measured on main): deleting `Body⁺`/`toProg`/one lowering about 60
(Bloat-Stage1); `Steps.Properties` (147) stays until `toScene` is proved to agree with `steps`
(then perhaps 60 of it become the `Delay`/`Par` induction); adds about 80 for `Embed` once the
agreement lemma exists, plus Clock/QClock (about 220 as spiked, which would be shared with
Stage 2's `TimeC` rather than duplicated).

Corrections to `plan/Unify.md` section 4 Stage 4:
1. "a coarser clock" is not a second type: it is the same `Clock` read through `ι`; compose by `at-compose`.
2. "nested clock by substitution" needs no new operation; it is `>>=` of `TimeC ⋆ –` (`nested-flat`).
3. The 60-line `Body⁺`/`Prog` collapse does not depend on Stage 4 and can go earlier; the
   spike shows `goBy` already works on `Prog`.
4. A pause is `Delay 1` in a `Par`-accumulating scene (shows persist), not a `Seq` boundary:
   `Seq` would hide the earlier content.  Seq is the right operation only between slides.

## 6. What landed (branch `deck-scene`, from a427adf)

1. **`Body⁺` is `Prog`** (-61 lines).  `BlockAwaitC = ProgC`, `Body⁺ X = Prog X ⊤`: a body that awaits is a
   `Slides.Input.Prog` over `Shape BlockC`; deleted `toProgC`, `toProg`, `toProg-bind`, `lowerCmd`,
   `lowerCmdBlock`, `lowerCmdBody`, `lowerCmdBody-bind`, `lowerCmdBody-lowerDeck`, `deckProg`;
   `presentBody` uses `Supports.lowerDeck`.
2. **`Steps` is the ℕ-clock reading of a scene.**  `sceneBy step?` sends a program that awaits to a
   `Scene (Maybe Leaf)` (`show c ; k = c ∥ k`, a step `Delay 1`, the end of the body `pure nothing`);
   `Slides.Anim.Perform.perform` (new, 46 lines, Hudak's `perform`: the algebra of `TimeC` into
   `ℕ × List (ℕ × –)`, each leaf with its start tick) and `page` (a command that starts after tick 0 is a
   fragment, notes and scripts never) give `stepsBy`, so `steps b = stepsBy isNext (elab b)`.  Deleted:
   `go`, `after`, `goBy`, `afterBy`, `wrapC`, `wrapL`, `stepL`, `Slides.Steps.Input` (merged), `bind-assoc`,
   `go-bind`, `goBy-bind`, `goBy-elab`, `afterBy-elab`, `stepsBy-elab`, `elab-bind`, `go-bind-elab`, `steps-lowered`
   (the mode pass and the whole bridge between its two copies; `steps-lowered` became `scene-lowered`, a mode-free
   induction).  The scene is a *pass-free* fold (no mode: the mode was the number of `Delay`s above).  Goldens
   are byte-identical.  The backends are untouched: `renderDeckBy` still takes a `Body → Body` per slide
   (`steps`, `presentBody b`), so Lower/Reveal/Plain read fragments from the scene through `stepsBy`.
3. **Proofs** (all `--safe --without-K`, no holes):
   * `Steps.Properties`: `dur-sceneBy` (the duration of a program's scene is its number of steps),
     `shown-chunks` (**step `j` shows the first `j + 1` chunks**: the scene sampled at tick `j` of the ℕ clock,
     `Slides.Time.Nat`, is the commands before the first pause then the first `j` later chunks),
     `machine-shown` (**the deck machine after `j` `next`s views exactly that**: `replay M j` is the tick `j`),
     `scene-elab` (the scene of `elab b` does not depend on the extra commands `C`).
   * `Lower.Properties`: `scene-lowered`, `steps-pipeline` as before.
   * `Anim.Sample.Properties.Nested`: `timeAlg-congruent` (the algebra of `Sample` respects equality of timed
     values for **every clock and all six connectives**, no clock law used) and `nested-flat` =
     `foldS-bind`: reading a substituted scene is reading with the leaf semantics substituted.
   * `Anim.Sample.Properties.Nat`: at the ℕ clock `seq-left`, `seq-right`, `hold-in` and **`loop-tick`**
     (`Repeat n` at tick `k * d + τ`, `k < n`, `τ < d`, shows its operand at `τ`: the Repeat tick law of
     `docs/TimeSwitch.md` section 8, for the clock ℕ).
   * `Input.Slides.Properties.Scene`: `Deck A = Scene (Scene A)` as a theory: `deckS : List Slide →
     Scene (Scene (Maybe Leaf))` (a slide is `Hold (pauses + 1)`, slides are in `Seq`), `flat = >>= id`,
     `deck-nested` (read slide by slide = read flat), `startOf-prefix` (slide `i` starts at the total length
     of the slides before it, which is `startOf`), `deck-shown` (**at position `total ss₁ + j` the flat deck
     shows what slide `s` shows at step `j`**: "slide `k` of an `n`-slide deck" as a fold).

## 7. Decisions and corrections to sections 1-5 (and to `plan/Unify.md`, not edited)

* **The deck type is not `Scene (Scene A)` in the code.**  `Slides.Core.Deck = DeckC ⋆ ⊤` stays: a slide is a
  generic effect (`slide o b : Deck`), which is what `do`-notation needs, and the free monad of `DeckC` is the
  free monoid on slides, i.e. `Seq` of slides modulo associativity and unit; `deckS` is the fold into the
  scene.  A literal `Seq` node would make `do` build binary trees by hand.  What *is* unified is the temporal
  layer: both levels are read by the one algebra `timeAlg`, in the one clock `Slides.Time.Clock`, and nest by
  `>>=` (`nested-flat`).  No second `Clock` or `TimeC`: the spike's `Clock.agda` (166 lines) and `QClock.agda`
  (56) are not ported.
* **Pause is a chunk in the scene, a click per command on the page.**  Section 3's "this is exactly `Steps`"
  was wrong: `Slides.Steps` wraps *each* command after the first pause in its own `fragment` (the existing
  caveat of `docs/Input.md`: machine positions are not physical fragment indices), whereas the scene
  `pause = Delay 1` shows a whole chunk at once (`shown-chunks`).  `page` keeps the old DOM (that is what keeps
  the goldens), so the page forgets which commands share a tick; two commands after one pause are two clicks
  in reveal.js but one position in `navM`/`startOf`.  The showcase deck's own text ("appears on the first
  step ... and so do these") reads as the chunk semantics; the fix is one attribute (`data-fragment-index` =
  the start tick) and it would change the goldens, so it is **not done**: the author's call.
* **`nested-at` needs more than `ClockLaws`.**  With the windowed `seqW` of `Sample` (the spike used the bare
  `seqT`) the pointwise law needs `+-assoc`, `(a + b) - a = b`, `a + b ≮ a`, and `a < b ⇒ c + a < c + b`
  (and `0 ≤ c + a`), none of which is in `ClockLaws`.  They are arithmetic for the clock ℕ, and
  `Sample.Properties.Nat` proves the three consequences used (`seq-left`, `seq-right`, `hold-in`).  A generic
  statement would add a `NestedLaws` record and its ℚ instance (the spike's `QClock` has four of the laws);
  **not done**, since the deck's positions are ℕ.
* **The machine's `view` accumulates across slides.**  `sem` wraps later shows *inside* the `await`, earlier
  ones outside, so `view (machine (deckBody ss))` after `n` `next`s contains the shows of *all* earlier slides
  (a `Par`), while the flat scene hides them (a `Seq`).  So `machine-shown` is stated for one body, and the
  deck level is stated by positions (`deck-shown`, `startOf-prefix`), which is what labels use.
* `Hold` filters, in `perform`, the events that start outside its window, as `holdT` does; `Repeat` lays copies
  end to end.  `perform` is not a homomorphism for `>>=` (the filter looks at absolute onsets): its nested law
  is `foldS-bind` with `perform` as the leaf semantics, not a list identity.

## 8. Not done

* The swap law `(a ⨾ b) ∥ (c ⨾ d) = (a ∥ c) ⨾ (b ∥ d)`, `dur a = dur c`: at ℕ it needs `Windowed b`, `Windowed d`
  (nothing after the end) and about 40 lines of `<ᵇ` case analysis; it is false without the hypothesis.
* The ℚ instance and generic-clock form of `nested-at`; `Drive`'s tick law.
* `LayoutShape.pause` and `stepped` are still in `Core` (the body type still carries `pause`; `elab` is its
  `await next`): making `pause` an awaited command at authoring time is the next deletion (about 30 lines:
  `elab`, `elabS`, `scene-elab`, the `pause` clauses of `pauses`, `renderLayout pause`), but it changes `Body`
  to a program over `Nav`, i.e. every example's type.
