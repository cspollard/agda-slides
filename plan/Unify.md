# Unifying diagrams, animations and decks: a plan

Status: proposal, nothing built. Branch `plan-unify`. Extends `plan/Plan.md` item 10.
Ground rules stand: free monads over containers, interpretation by algebras, stdlib
`Container.*` theory, laws proved where possible, `--safe --without-K`, executables must not
import `.Properties` modules (`tests/check_closure.py`).

## 1. Where we are

Three languages, each already "a free monad over a container, folded by an algebra":

| Language | Container | Leaves | Semantics |
|---|---|---|---|
| Diagram `Dia S` | `DiagramC S` (primitives, `Beside/Above/Atop`, `Place/Overlay`, `Named/Connect`) | primitives | `layout : Dia S → Layout S`, natural in the scalar `S` |
| Animation `Anim S T` | `AnimC` (`Seq`, `Par`) | `Seg S` = a `Track ℚ` (itself a free monad) + a `SegBody` (`blackBox`, `template : Dia (Expr ⊤)`, `discrete : Dia (DExpr ⊤)`) | `foldA`; `dur`; `frameAt` (ℚ), `bodyAt` (floor ticks); shipped as `data-param` |
| Deck | `DeckC`, `BlockC = ContentC ⊎ LayoutC` (stratified) | slides, blocks | `Steps` (pause elaboration), backends |

Time-varying things are already half-unified. A `template` segment is a diagram whose scalars
are `Expr ⊤`, the free `Ops`-algebra on one variable `t`; evaluating at a time is a monad
algebra (`evalWith`, `evalWith-unique`), and layout commutes with it (`layout-natural`).
So the semantic core of "functional reactive" is there: a time-varying diagram is a diagram
over a scalar that has a free variable. What is *not* unified is that the temporal structure
(`Seq`, `Par`, tracks, loops, phases, steps) lives in three separate places, with separate
proofs (`discrete-assembly`, `frameAt-assembly`, `phases-active`, `Steps.go-bind`).

## 2. What "FRP" has to mean here

Classic denotation (Elliott–Hudak): `Behavior A = Time → A`, `Event A = Time × A`.
A literal implementation (arrows, signal functions, `switch`) loses what we have: the
program has dynamic structure, so it cannot be laid out once symbolically and shipped as
formulas, and it cannot be proved against a closed-form assembly.

So the proposal is **static-structure FRP, as a free monad**:

1. **Behaviours are terms with free variables.** `Beh V S = Expr V` over the scalar signature
   (the layered `CoreC ⊎ SubC ⊎ …`). The variable set `V` is the *context* of the reactive
   program: `τ` (time), and later a step counter, scroll, a slider. A closed behaviour is a
   constant. This is exactly the existing `Expr`, with `V` no longer `⊤` by convention.
2. **Time transformations are substitution (Kleisli composition).** Delay, stretch, reversal,
   easing as time-warp are `subst` along `τ ↦ e(τ)`. `subst-bind` and `evalWith-unique`
   (already proved) give the semantics for free: sampling a warped behaviour is sampling the
   original at the warped time.
3. **Temporal structure is a second container `TimeC`** (`Seq`, `Par`, then `Delay`, `Repeat`,
   `Hold`), with leaves the spatial program. A scene is
   `Scene S = (TimeC ⊎ DiagramC S) ⋆ ⊥`: `Container.Sum` already gives the copairing of
   algebras.
4. **Interpretation is an algebra into `Timed A`**, `ℕ × (Time → Maybe A)` (duration and a
   partial function of time, as `Timed` in `Slides.Anim.Continuous`). Spatial operations act
   *pointwise* (the reader applicative), temporal ones are `seqAt`/`parAt`.
5. **Events are boundaries, not a dynamic primitive.** `Seq` is "switch at a statically known
   time". Genuine `switch`/`until` with data-dependent times, stateful `integral`, and
   input from the user are *out of scope* for the shippable core; if wanted they are a
   separate, non-symbolic layer (see risks).

Note the consequence: the monad of the free structure is used for *substitution and
composition of programs*, not for dynamic dependence on values. That is what keeps shipping
and proofs possible.

## 3. Staged plan

Each stage ends with `make check`, `make test`, `make test-negative`, the browser tests, a
closure check, and a compile-time/memory measurement against the figures in Plan item 9. Each
stage keeps every existing theorem as a corollary or states why it moved.

**Stage 0: decide and de-risk (no change to `main`).** Spike in `src/Slides/Spike/`:
- one `TimeC`, one `Timed`, and the pointwise lift of the *layout* algebra to `Timed (Layout S)`.
  Question: does `Beside` of a present and an absent side (the `Maybe` in `Timed`) have the
  right unit? `Par` uses `Atop` with absence as unit today (`Timeline.merge`); check it is the
  same law.
- prove the lifting lemma `sample (fold (lift alg) t) τ ≡ fold alg (restrict t τ)` for the
  spatial fragment. If this lemma is not cheap, the whole plan is not.
- measure the instantiation cost (the generic `ParamCorrect` cost 53 s; do not repeat that).
Go/no-go: lifting lemma proved in under about 150 lines and under about 30 s.

**Stage 1: time as a variable context.** Generalise `Expr ⊤` to `Expr V` in `SegBody.template`
with `V = Time`. No behaviour change. Add `Ease` to the scalar signature as a unary
operation (a new layer, as `SubC` and `EuclidC` are) so an easing is a term, not a `Track`
side-table; the JS player already implements easings. `Track` becomes a derived notion: a
piecewise behaviour built from `Seq` of `Ease` pieces. Needs an ordered layer (`Lt`, `clamp`)
in ℚ, parallel to `EuclidC`'s ℕ-only `Lt`.

**Stage 2: one temporal container.** Replace `AnimC` by `TimeC`, and `Seg` by "a scene node
with a duration". `foldA`, `dur`, `animAt` become instances of the generic `Timed` algebra.
Expected to delete or shrink: `Anim.Assembly`, `Anim.Assembly.Leaf`, `Anim.Assembly.Continuous`
(three proofs of "assembly" for three readings of time), parts of `Timeline`/`Footprint`.
Proofs to re-derive: `discrete-assembly`, `frameAt-assembly`, `atop-ι`, `sampleAt-ι`.

**Stage 3: loops, phases, steps as time operations.** `Repeat` replaces `Loop`; `both` becomes
`Repeat` of a stepped scene; `pause` becomes a `Seq` boundary in a *discrete* clock, so
`Slides.Steps` is an instance of the same temporal elaboration. Re-derive `phases-active`,
`enc-sem`, `Steps.go-bind`. Backends read fragments off `Seq` boundaries.

**Stage 4: decks.** A slide body is a scene in step time, a deck is a `Seq` of slides in a
coarser clock, an animation inside a slide runs on a nested clock (clock domains compose by
substitution, as in 2). Keep the `ContentC`/`LayoutC` stratification: unify the *temporal*
layer and the *carrier-independent* algebras, not the carriers (HTML flow content and
geometric layout stay different algebras on the same signature of time).

**Stage 5: one evaluator, generated.** With the signature now the single source, generate
the JS `ev` from it (closes the "tested, not proved" gap in the direction of one source), and
fold the player's phases/params paths into one.

## 4. Pros and cons

**Pros**
- *Less code, fewer duplicated proofs.* Today there are three "assembly" proofs and three
  readings of time (ticks, phases, ℚ); they become instances of one lifting lemma.
- *Principled.* Time-varying values are free variables of an `Expr`; time transformations
  are Kleisli substitution; temporal structure is a container; semantics are algebras and
  `evalWith-unique`. Nothing outside Containers/FreeMonads/Algebras.
- *Compositional by construction.* Delay, stretch, reverse, nested clocks (slide in deck,
  animation in slide) all fall out of substitution, with laws from `subst-bind`.
- *Shippable.* Static structure keeps everything symbolic: one layout, formulas, shared
  subformulas, `Share`/`Phases` encodings still apply.
- *Single player, single evaluator*, generated from the signature.
- *Authoring.* A still diagram is a constant animation, and a slide is a scene; one DSL.

**Cons and risks**
- *Large change to proved code.* Roughly 40 modules touch `Anim`; all assembly and
  phases proofs are re-derived, not just moved. Needs a firm go/no-go at Stage 0.
- *Compile time and memory.* Generic proofs over a sum container instantiated at several
  algebras have been our worst performers (`ParamCorrect`, `Continuous*`); memory is already
  ~6 GB for `make check`. A generic lemma instantiated at layout, names, footprint and
  phases may cost more than three direct ones.
- *Partiality.* `Timed` needs `Maybe` (absent outside `[0, dur)`); spatial ops must treat
  absence lawfully (units). The current `merge` shows it works for `Atop`, but `Beside`,
  `Above`, `Place` have no obvious unit; they may need `Par`-only absence.
- *Easing and nonlinear ops in the signature* have no ℕ meaning and are not
  ring homomorphisms; the discrete reading (`units`, floor) must stay a separate
  interpretation, so "one semantics" is really two (ℚ, ℕ) with a proved relation on whole ticks.
- *FRP promises we will not keep.* No data-dependent `switch`, no `integral`/state, no user
  input in the shippable core. If someone wants those, they live outside the symbolic
  pipeline, and the docs must say so plainly.
- *Decks are a poor fit for a single time axis.* HTML flow content, citations, numbering and
  figures are not temporal; forcing them into `TimeC` risks an abstraction that is mostly
  ceremony. Mitigation: Stage 4 is gated and may be dropped without harming Stages 1 to 3.
- *Function-valued semantics under `--without-K`.* `Time → A` equality needs pointwise
  reasoning (`Eq`-respect, as in `evalWith-unique`); every statement is pointwise.

## 5. Alternatives considered

- **Do nothing; share only a `Timed` module.** Cheapest; removes little duplication, leaves
  three proof families. Fallback if Stage 0 fails.
- **Arrowised FRP (Yampa-style signal functions).** Most expressive, but dynamic: cannot be
  shipped as formulas and our proofs do not apply. Rejected.
- **Make `Dia` itself time-indexed (`Dia` over `Behavior`).** This is Stage 1 taken to the
  limit and is already what `template` does; the missing piece is only the temporal
  container, so we do not need a new diagram language.
- **Reader-monad semantics only, no free monad for time.** Loses `Seq`/`Par` as data (for
  `dur`, footprints, phases, symbolic shipping). Rejected: violates the free-monad ground rule.

## 6. Recommendation

Do Stages 0 and 1 (low risk, mostly reinterpretation of what exists), then decide on Stage 2
from the Stage 0 numbers. Treat Stages 3 and 4 as separately approvable. Do not promise
dynamic FRP; promise *static-structure reactive programs with a closed-form, proved
semantics*, which is what the backends can actually compile.

## 7. Questions for the author

1. Is user input (clicks, a slider) a goal, or only time and step?
2. Is dropping the `blackBox` segment (flipbook-only) acceptable once templates cover the
   decks, or must arbitrary `ℚ → Dia S` stay?
3. Should the ℕ/discrete reading remain a first-class backend (reveal fragments), or become
   "the ℚ reading sampled at ticks" with the relation proved once?
