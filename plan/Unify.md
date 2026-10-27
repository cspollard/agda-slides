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
5. **User input is a parameter of the program, not a dynamic primitive.** Commands
   (`next`, `prev`, `goto k`, a clock tick, a click on a named element) form a type `C`;
   a program is indexed by the commands it awaits, `Prog C S`. `await c` is a one-child
   operation of a container `AwaitC C = C ▷ (λ _ → ⊤)`; today's `pause` *is* `await next`
   (`Slides.Steps` is its first elaboration). Alternatives (which of several commands arrives)
   are an operation with one child per command. Time itself is a command, `tick`, so a backend
   with no clock (print, a static page) simply does not support it. See section 3.
6. **Events are boundaries, not data-dependent switching.** `Seq` is "switch at a statically
   known time"; a command is "switch when this input arrives". Genuine `switch` on a *value*,
   stateful `integral`, and unbounded history are out of scope for the shippable core.

Note the consequence: the monad of the free structure is used for *substitution and
composition of programs*, not for dynamic dependence on values; the only dynamism is the
finite control graph that the awaited commands induce. That is what keeps shipping
and proofs possible.

## 3. User input

Requirement: slides change by user commands, so input comes first. The program must be
parametric in the commands it uses; a backend supports only a subset; composing programs is
only valid when their inputs do not overlap.

**Design.**
- *Commands are an abstract type* `C` (a datatype of intents, not of keys: `next`, `prev`,
  `goto n`, `tick`, `click name`). Programs are `Prog C S = (SceneC S ⊎ AwaitC C) ⋆ A`, the free
  monad on the sum container (`Container.Sum` again). Smart constructors: `await c`,
  `onEither (c₁ ⇒ p₁ ∣ c₂ ⇒ p₂)`, `repeat`.
- *Meaning is a machine, obtained by an algebra.* Fold a program into
  `Machine C = (state Q, step : Q → C → Q, view : Q → Frame-in-time)`: a Moore machine, the
  coalgebra dual to the free monad. Syntax stays a free monad; the running system is the
  coalgebra the algebra produces, so cycles (back/forward) are fine without recursion in the
  syntax. A `Seq` of slides is a machine whose `next` moves one state on; `Par` of
  programs is the *product* of machines, with `view (q₁,q₂) = view₁ q₁ ∥ view₂ q₂`.
- *Parametric in commands, composition disjoint by construction.*
  `_‖_ : Prog C₁ A → Prog C₂ A → Prog (C₁ ⊎ C₂) A`: each side reacts only to its own
  summand, so the disjointness condition holds by construction and is a type, not a check.
  Sharing one physical input between two parts is not composition; it is a **binding**.
- *Backends declare what they support, and bind commands to inputs.* `Backend.supports ⊆ C` (superseded: a partial embedding `Nav ⊎ C → Maybe S`, section 4b),
  plus `bind : C → Input` (reveal: arrow keys, overview, hash `#/n`, fragments; plain: buttons;
  print: none). Two commands bound to the same input are a conflict, checked at binding
  (decidable injectivity, reported like our existing negative tests `OverlappingPar`,
  `NonUniformBoth`). A program that uses a command the backend does not support is either
  rejected or *lowered*: `Container.Lowering` already exists for this (`supports`/`uses`,
  Plan item 6), so an animation lowers to its rest frames on print, a clockless page to its
  steps, and so on.
- *Decision for the author* (section 8, Q4): if you want "overlap is a type error at the point
  of composition" even for a global key vocabulary, we index by a list `uses : List C` and
  require `Disjoint uses₁ uses₂` (decidable, a `True` argument as the DSL already does). It is
  closer to your sentence, costs a list-reasoning layer, and makes composition partial. The
  sum-indexed design is cheaper and total, and moves the same check to binding.

**Proof obligations (planned).**
- *Elaboration is a homomorphism:* `machine (p ‖ q) ≅ machine p × machine q` (product of
  Moore machines), and `machine (p ⨾ q)` is sequencing.
- *Lowering is sound:* a program that uses only supported commands has the same behaviour
  under the backend and under the generic semantics; unsupported ones agree with the
  documented default.
- *Pause is `await next`:* `Slides.Steps` results (`go-bind`) restated as an instance.
- *Time is just a command:* the continuous semantics is the machine run on `tick`s of real
  duration (the limit of its sampling), with `sampleAt-ι` as the relation on whole ticks.

## 4. Staged plan

Each stage ends with `make check`, `make test`, `make test-negative`, the browser tests, a
closure check, and a compile-time/memory measurement against the figures in Plan item 9. Each
stage keeps every existing theorem as a corollary or states why it moved.

**Stage 0: decide and de-risk (no change to `main`).** Spike in `src/Slides/Spike/`:
- `AwaitC C`, the sum with `DiagramC`, and the fold into a Moore machine `Machine C`; show
  `pause` is `await next` and that `Slides.Steps` falls out as an instance.
- one `TimeC`, one `Timed`, and the pointwise lift of the *layout* algebra to
  `Timed (Layout S)`. Does `Beside` of a present and an absent side (the `Maybe` in `Timed`)
  have the right unit? `Par` uses `Atop` with absence as unit today (`Timeline.merge`).
- prove the lifting lemma `sample (fold (lift alg) t) τ ≡ fold alg (restrict t τ)` for the
  spatial fragment, and the product lemma `machine (p ‖ q) ≅ machine p × machine q`.
- measure the instantiation cost (the generic `ParamCorrect` cost 53 s; do not repeat that).
Go/no-go: both lemmas proved in under about 150 lines each and under about 30 s.

**Stage 1: user input as a parameter (first, because slide change needs it).** Introduce
`C`, `AwaitC`, `Prog C`, `machine`, `supports`, `bind`, and the conflict check; port
`pause`/fragments, reveal's next/prev, and the plain backend's buttons onto it with
*no change in output* (goldens and browser tests unchanged). `Lowering` handles unsupported
commands. Add negative tests: a backend that cannot bind a used command; two commands bound
to one input.

**Stage 1b: time as a variable context.** Generalise `Expr ⊤` to `Expr V` in
`SegBody.template`, `V` containing the time variable. No behaviour change. Add `Ease` to
the scalar signature as a unary operation (a new layer, as `SubC` and `EuclidC` are), so
an easing is a term instead of a `Track` side-table; the JS player already implements
easings. `Track` becomes derived: `Seq` of `Ease` pieces. Needs an ordered layer (`Lt`,
`clamp`) in ℚ parallel to `EuclidC`'s ℕ-only `Lt`.

**Stage 2: one temporal container.** Replace `AnimC` by `TimeC`, and `Seg` by "a scene node
with a duration". `foldA`, `dur`, `animAt` become instances of the generic `Timed` algebra.
Expected to delete or shrink: `Anim.Assembly`, `Anim.Assembly.Leaf`, `Anim.Assembly.Continuous`
(three proofs of "assembly" for three readings of time), parts of `Timeline`/`Footprint`.
Proofs to re-derive: `discrete-assembly`, `frameAt-assembly`, `atop-ι`, `sampleAt-ι`.

**Stage 3: loops, phases, steps as time and input operations.** `Repeat` replaces `Loop`; `both` becomes
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

## 4b. Stage 0 results (spikes `spike-timed` 96f4bd8, `spike-input` 6912a6f; unmerged)

Both halves pass the go/no-go with a wide margin: no postulates, no holes, no instance search,
`--safe --without-K`; each spike re-checked independently.

**Timed lift** (`src/Slides/Spike/Timed*`, 374 lines, about 103 lines of proof, 4.7 s, 1.8 GB):
- `TimeC` (`Seq`, `Par`, `Hold n`, `Delay n`), `SceneC S = TimeC ⊎ DiagramC S`,
  `Scene S = SceneC S ⋆ ⊥`, carrier `Timed (Maybe A)`.
- **Lifting lemma, as proved:** naturality along any algebra homomorphism `Φ : A → B`
  into an extensional target, `Rel Φ (sample αB t) (sample αA t)`; with `αA` the term algebra
  it gives `sample α t τ ≡ Maybe.map (fold α) (restrict t τ)` and equal durations. Covers
  the temporal operations too. Instantiated at layout in one line (`lifting-lemma-at layoutAlgebra
  layout-ext`), no slowdown. (My earlier statement was not typable: it needs the `Maybe.map`.)
- **Absence is strict.** `Beside`, `Above`, `Atop`, the label operations and `Overlay` are
  present only when all children are; `Place`, `Named`, `Connect` map over the child; only
  `Hold`/`Delay` create absence; only `Par` is lenient (`Atop` with absence as unit, as
  `Timeline.merge`; `par-is-atop` is `refl`). The lenient design is *unlawful* for `Overlay`
  (`overlay-no-unit`: the frame has the declared size whatever the children). This replaces
  the plan's open question about units.
- **Corrections:** extensionality (a pointwise-congruence condition, 14 trivial clauses for
  layout) replaces funext; bare primitives have no presence window, so Stage 2 must put
  them under `Hold` (or take durations in `ℕ∞`); `seqAt` shows its left operand at
  negative times, so `Seq` needs a window guard; `Container.Sum.copair` is stated on
  setoid `Func`s, so a Set-level copairing is needed for plain `cata`.
- **Not done:** `Repeat`; re-deriving `frameAt-assembly` and `discrete-assembly` (needs
  an embedding of `Anim ℕ (Seg ℕ)` into `Scene` and the faithful ℕ→ℚ bridge); constant
  behaviours of `inj : Dia S → Scene S`.

**Input machines** (`src/Slides/Spike/Input/*`, product lemma about 135 lines, 1.7 s, 1.4 GB):
- `AwaitC C = C ▷ ⊤`, `ProgC C = SceneC ⊎ AwaitC C ⊎ ParC`; `Machine C`
  (state, init, step, view) as the carrier of a Kleisli fold `sem`; adapters along partial
  decoders `D → Maybe C`.
- **Proved:** `product` (`machine (p ‖ q) ≅ machine p ⊗ machine q`, with `MIso`, a state
  bijection preserving init/step/view, no funext), `sem-bind` (the fold is a monad
  morphism), `seq-machine`, `await-seq`, `lift-lemma` (`sem (mapP f p) ≅ liftE h (sem p)`).
- `Nav` (with `gotoLabel`), `pause = await next` (`Steps` elaboration: `after-elab`,
  `after-seq`, `hasAwait-bind`), `Backend` (partial embedding `inj : Nav ⊎ C → Maybe S`,
  `NavTotal`, `printB` provably cannot present a deck, `lowerDeck`, decidable `conflict?`
  for finite tables), `navM` (replays `next`s; `view-next`, `prev-next`).
- **Corrections:**
  1. *Choice cannot be `OnC C`.* A morphism `OnC C₁ ⇒ OnC (C₁ ⊎ C₂)` does not exist
     (`no-OnC-inl`), so `‖` could not be a `translate`. Choice must carry the offered commands
     in its shape (shape `List C`, positions the offered ones, with `C → Maybe A` in the
     machine). Not built; only `AwaitC` is in.
  2. *`‖` needs `ParC = ⊤ ▷ Bool`*, and a free-monad `par` node duplicates its
     continuation, so `(p ‖ q) >>= k` runs `k` twice. Either `‖` only at the top, or `par`
     with a join. Unresolved; decide in Stage 1.
  3. *`bind : C → Input` fails for families* (`goto n`, `gotoLabel s`, reveal's `#/n`). The
     decidable conflict check works for finite tables only. Bind constructor *kinds*
     (finite) and decode families: `decode : Input → Maybe Command`, with conflicts then
     only between decoders. Not built.
  4. *Embedding direction.* Section 3 said `supports ⊆ C`, section 8 `Nav ↪ supports`; the
     spike implements a partial embedding of commands into the backend vocabulary. This plan
     now means that one (the section 3 phrase is superseded).
  5. `prev`, `goto`, `first`, `last`, `gotoLabel` are not awaited; they are interpreted by a
     separate machine (`navM`) that replays `next`s, and `gotoLabel` needs a `label`
     operation and a label table (not built).
  6. Unsupported commands are lowered by skipping the `await` (jumping on), shown per
     operation and by examples; the whole-program lowering soundness theorem is not proved.
  7. The view is an accumulating list (Beamer `pause`), not the plan's `Frame-in-time`.

**Decisions this forces for Stage 1** (author to confirm): (a) `‖` only at the top of a
program, or `par` with a join (recommend: top-level, with the join deferred until Stage 2
needs it); (b) choice via commands in the shape; (c) binding by kind plus decoders; (d)
strict absence with `Hold` around primitives for Stage 2.

## 5. Pros and cons

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
- *Input is uniform.* Slide change, fragments, loops and a clock are all `await`; backends
  differ only in `supports` and `bind`, with unsupported commands lowered instead of failing.
- *Authoring.* A still diagram is a constant animation, and a slide is a scene; one DSL.

**Cons and risks**
- *Input adds a coalgebra.* The control machine is a second carrier next to the algebra into
  `Timed`; the product lemma and lowering soundness are new proofs, and `Lowering` has to
  carry command sets (`supports`/`uses`) that it does not carry today.
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
- *FRP promises we will not keep.* No value-dependent `switch`, no `integral`/state. User
  input is supported only as a finite alphabet of commands with a finite control graph; a
  free-form input (a pointer position, a slider value) is a variable of a behaviour, not a
  command, and needs its own treatment (not in Stage 1). If someone wants those, they live outside the symbolic
  pipeline, and the docs must say so plainly.
- *Decks are a poor fit for a single time axis.* HTML flow content, citations, numbering and
  figures are not temporal; forcing them into `TimeC` risks an abstraction that is mostly
  ceremony. Mitigation: Stage 4 is gated and may be dropped without harming Stages 1 to 3.
- *Function-valued semantics under `--without-K`.* `Time → A` equality needs pointwise
  reasoning (`Eq`-respect, as in `evalWith-unique`); every statement is pointwise.

## 6. Alternatives considered

- **Do nothing; share only a `Timed` module.** Cheapest; removes little duplication, leaves
  three proof families. Fallback if Stage 0 fails.
- **Arrowised FRP (Yampa-style signal functions).** Most expressive, but dynamic: cannot be
  shipped as formulas and our proofs do not apply. Rejected.
- **Make `Dia` itself time-indexed (`Dia` over `Behavior`).** This is Stage 1 taken to the
  limit and is already what `template` does; the missing piece is only the temporal
  container, so we do not need a new diagram language.
- **Reader-monad semantics only, no free monad for time.** Loses `Seq`/`Par` as data (for
  `dur`, footprints, phases, symbolic shipping). Rejected: violates the free-monad ground rule.

## 7. Recommendation

Do Stage 0, then Stage 1 (input; low risk, because `pause` and navigation already are this
shape) and 1b (mostly reinterpretation of what exists), then decide on Stage 2 from the
Stage 0 numbers. Treat Stages 3 and 4 as separately approvable. Do not promise
value-dependent FRP; promise *static-structure reactive programs with a closed-form, proved
semantics*, which is what the backends can actually compile.

## 8. Answers so far and open questions

Decided (author): user input comes early, as a parameter of the program (section 3). `blackBox`
segments can go once templates cover the decks (a flipbook remains as a lowering target,
not as syntax).

**Discrete time: is there a downside?** Keep it; the question is only which role it plays.
- *Events are discrete, behaviours are continuous.* That is the FRP split, not a compromise:
  commands, steps and slide changes arrive at instants and index a finite state; within a
  state, a behaviour is a function of real time. Reveal fragments and the control machine
  are naturally discrete (`ℕ`-indexed states).
- *Benefits of the ℕ reading:* exact arithmetic (our reference deck compares exactly at ticks;
  no rounding in goldens), decidable equality, hash-consed shared formulas, `mod` for loops.
- *Costs:* (1) two semantics, tied by `sampleAt-ι` only on whole ticks; (2) between ticks the
  discrete reading holds the previous frame, so smooth playback needs the ℚ reading anyway;
  (3) the `Euclid` operations (`DivBy`, `ModBy`, `Lt`) mean something only in ℕ, so
  discrete templates cannot be mixed with fractional time (the current "whole animation is
  discrete" restriction); (4) non-integer stretch or tempo changes need rounding (Hudak's
  `zero (a + b)` issue that `Anim.Syntax` already notes).
- *Resolution proposed:* ℚ is the one semantics of behaviours; ℕ is the *clock of the
  control machine* and the reading of a ℚ behaviour at whole ticks (relation proved once,
  `ι` is a faithful homomorphism). Add `floor`, `mod`, `lt` to the ℚ ordered layer so the
  `Euclid` templates have a ℚ meaning, and then the ℕ reading is a restriction, not a
  separate language. No downside to keeping discrete *control*; the only thing to avoid is
  keeping two full *value* languages for ever.

Decided (author), in answer to the earlier open questions:
- **Disjointness:** total composition at `C₁ ⊎ C₂`; the conflict check is at binding (the
  sum-indexed design). No `uses` index.
- **Clock:** `tick` is a command like any other; backends without a clock lower animations to
  rest frames.
- **Inputs:** the framework is parametric in the command type from the start; no fixed
  input vocabulary is baked into the language. A *deck* is a program that requires a
  standard navigation vocabulary, `Nav = next | prev | goto n | first | last` (and the
  fragment steps that `pause` produces), so a deck is `Prog (Nav ⊎ C) …`: any backend that
  presents decks must support `Nav` (reveal: arrows, hash, overview; plain: buttons). Extra
  commands (`click`, `tick`, chords, sliders) are further summands that a deck may add and
  a backend may or may not support. A backend that lacks `Nav` cannot present a deck at
  all (rejected, not lowered); one that lacks an extra command lowers it.

Consequences for the stages: Stage 1 defines `Nav` and a `Backend.Supports` interface
(`supports : Set`, an embedding `Nav ↪ supports`, `bind`) first; `Slides.Steps` and reveal's
and plain's navigation are ported onto it with unchanged output. Stage 0's spike includes
the `Supports` embedding and checks that the conflict check at binding is decidable and cheap.

Open:
1. Which commands beyond `Nav` come first: `tick` (clock) is assumed; `click name`, key
   chords and a slider value are candidates. A slider value is a variable of a behaviour,
   not a command, and needs its own treatment.
2. Should `Nav` include `goto` by name (a slide label) as well as by index, so decks can be
   linked and reordered without renumbering?
