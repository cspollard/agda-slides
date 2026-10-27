# Stage 4 spike: is "a deck is a scene" coherent?

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
