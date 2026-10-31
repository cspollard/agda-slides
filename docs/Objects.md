# The objects, and the maps between them

The one document every contributor and agent reads first.  Ideas and maps, not code names.
Decisions are marked **[decided]**; the rest are defaults to revisit only with a reason.

## Principles
- Nontrivial types are free algebras of a signature (free monads over containers), so that
  substitution is bind, folds are algebras, and relations between languages are lowerings
  (Kleisli maps; an injection is the special case) and homomorphisms.  Every type must say which
  of these it is.
- The container spine has one fold, `pfold`; `Alg.fold` is `pfold` of an algebra's handler.
  `fold-fusion` (homomorphisms commute with folds) is derived from `fold-unique`.  The free
  monad is the one from the adjunction `Free ⊣ Forget` (algebras to setoids); `bind` is its
  fold.  Sums of signatures are eliminated by `copairL`.
- Identity and composition laws are proved where the structure is stated, once, generically
  (in `Container.*`), never re-proved per language.
- Meaning first (denotational design): fix the semantics, then show each implementation is a
  homomorphism of it.  Literature is the compass (below).
- No instance search in core.  `--safe --without-K`.  A new layer must delete or port more than
  it adds.

## How the objects relate
Each pair of objects is related by a map of a named *form*: a **split mono** (a section `s` and a
retraction `r` with `r ∘ s ≈ id`), a **sub-object of meanings** (a subset closed under the
operations), an **extension** of a signature (`C ↪ C ⊎ E` by `translate inl`, with a lowering
`copairL ret h` as retraction), a **reindexing** (precomposition with a map of inputs), a
**homomorphism** of models, or none.  A status is *holds* (a theorem, at file:line under `src/`),
*planned* (a Phase 9 step of `plans/TODO.md`), or *does not hold* (and why).

**Three meanings, independent of syntax.**  Every language is a free algebra whose fold lands in
one of three domains, all setoids at level 0 with pointwise equality (no function
extensionality).
- *Spatial*: `Layout S`, a frame with placed drawings and anchors.  Translation is an `Action` of
  `(S×S, ⊕)`; sizes are folds into envelope semigroups.
- *Temporal*: models of the temporal theory (the scene signature with Hudak's equations).
  `Timed X` (a duration and "time to maybe-value") and `Media X` (a duration and an event list)
  are models; reading the events is a model homomorphism `Media → Timed` (`events-sample`,
  Scene/Sample.agda:340).
- *Interactive*: behaviours `Beh_C O = List C → O`, the terminal coalgebra of the Moore functor
  `X ↦ O × (C → X)`.  Covariant in the output (`mapO`), contravariant in the words (`reindex`).
  When `O` is a model of a theory, `Beh_C O` is the power `O^(List C)`, so every law of `O` holds
  for behaviours.  Today `Machine`, `obs`, `final` and `CoHom`/`unique` are by hand
  (Program/Machine.agda).  As `Terminal (F-Coalgebras Moore)` with `mapO` and `reindex`: planned
  (S1).  The power-model theorem: planned, later (S2).

**The chain of meanings: Plot ⊂ Diagram ⊂ Animation ⊂ Program.**  Each step adds a dimension
(the fixed frame is dropped, then time is added, then input), and the smaller object sits in the
larger as the part that ignores the new dimension.
- *Plot ⊂ Diagram*, a sub-object.  Rendered plots are the drawings of size exactly `W × H`, a
  subset of `Dia ℕ` closed under overlay in that frame; `size-render` (Plot/Laws.agda:25) proves
  that `render` lands in it.  `render` itself is not an inclusion: clipping, rounding to pixels
  and the approximate logarithm lose information, and it is not a monoid homomorphism on whole
  plots (legend and axes depend on every series).  At most the marks layer is one, for fixed
  axes.  `Framed W H` as a Σ type with its overlay, and `render` into it: planned (S5).
- *Diagram ⊂ Animation*, a split mono.  Section: a still, `pure` (the unit of the scene monad;
  `liftDia` first, for a `Dia ℕ`).  Retraction: read one frame, the first (`firstFrame`,
  Backend/Animation.agda:248) or the last (`animationFinal`, Deck/Lower.agda:177).
  `diagram-const` (Scene/Animation.agda:83) is the pointwise law: a still reads as its diagram at
  every `t ≥ 0`.
- *Animation ⊂ Program*, a sub-bialgebra.  Section: `inject = translate inl`, whose meaning is a
  constant behaviour (`constB`).  Constants are closed under every scene operation (which acts
  pointwise, `prodB`) and under every command (the tail of a constant is itself).  Retraction:
  `hd`, the output before any command, a map of scene algebras.  `inject-const`
  (Program/Sem.agda:128) is the commuting square for scenes.  Generic in the signature
  (`sem-inject`), with `hd` a named map: planned (S1).
- *Deck is not a sub-object of Program*; it is a **reindexing**.  The step clock is the free
  monoid on one command, `List ⊤ ≅ ℕ`, so the ℕ-reading `visible (flat d) : ℕ → Maybe Flow` is a
  one-command behaviour (a stream).  Navigation precomposes it with the position map
  `runs navM zero : List Nav → ℕ`: `feed (deckM d) cs ≡ visible (flat d) (runs (deckM d) zero cs)`
  holds by definition (Deck/Machine.agda:88).  The position map is not a monoid homomorphism
  (`prev`, clamping at the ends), which is why `prev` and `goto` need no history.  "A deck is a
  program" holds per slide (`pause-agree`, Deck/Program.agda:84: `elab` of one slide after `k`
  nexts shows its first `k + 1` chunks), not per deck: `elab` keeps the sequence of slides as a
  scene operation and a behaviour is read at time 0 after each command, so slide 2 never shows.
  Removing slide 1 on `next` needs preemption, which `ProgC` lacks **[decided]**: it reopens full
  FRP.  The deck behaviour stated once, `pause-agree` restated against it: planned, later (S3).
- *Backend support* is a reindexing too: a backend that binds a subset of the commands means the
  program's behaviour precomposed with `mapMaybe dec` (`lower-sound`, Program/Supports.agda:147).

**Extensions of signatures.**  Syntax grows by sums `C ⊎ E` (Swierstra).  Each extension is a
split mono `translate inl : C ⋆ X → (C ⊎ E) ⋆ X`, and its retraction is a lowering that keeps
`C` and eliminates `E`, `lower (copairL ret h)`.
- Curve: `Dia⁺ S = (DiagramC S ⊎ CurveC S) ⋆ ⊥`; section `inject` (Diagram/Curve.agda:57);
  retraction `lowerDia`, the lowering by `lowerCurve = copairL ret (sample the curve)`;
  `lower-inject` (Diagram/Curve/Properties.agda:17).
- Program: `ProgC T D C = SceneC T D ⊎ AwaitC C`; section `inject`; retraction `skip`, the
  lowering by `skipOp = copairL ret (λ _ → pure tt)` (every wait satisfied); `skip-inject`
  (Program/Syntax.agda:56).
- Plot: content `(DiagramC ℕ ⊎ MarkC) ⋆ ⊥`, lowered by `copairL ret renderMark`: planned (S5).
  Today content is a list of series; only the comment at Plot/Render.agda:155 says this.
- The three proofs are one lemma, `lower (copairL ret h) (translate inl t) ≈⋆ t`, in
  `Container.Sum.Properties`: planned (S1).

Mind the direction: Diagram ⊂ Plot in *syntax* (plot content will contain diagrams), while
Plot ⊂ Diagram in *meanings* (every plot renders to a framed diagram).  The first is a split mono
of free algebras, the second only a subset of meanings.

**Reading at one instant.**  `firstFrame`, `now t = proj₂ t 0 nothing` (Deck/Program.agda:77)
and `hd` read at the start; `animationFinal` reads at the end.  Each is a retraction of a
constant section above, and a model homomorphism.  The read-at-start law, stated and proved
once: planned, later (S2), and only if its conditional laws stay small.

**Time: three clocks.**  The deck's step clock ℕ (`Slides.Deck.Clock`), the wall clock ℚ of
animations, and a driver's local time (a moving value, `Scene.Moving`); `Scene.Tick` relates the
first two along `ι`.  **[decided]** Each command restarts the real-time reading: in
`Beh_C (Timed X)` the output after a word is read from time 0 (`awaitB c k (c ∷ cs) = k cs`).
This is the semantics of random-access navigation: the output depends only on the position, and
content of earlier steps reads as settled.  It is not real-time interaction (a loop that keeps
running across a key press).  Should that be wanted, commands become `T × C` (a delay and a
command) and outputs `O^T`, with no new machinery.

**One notion of step (a known bug).**  "Advance on `next`" is spelled five ways: `pause` items
(chunks, then `delay 1`), `elab`'s waits, the `fragment` block, incremental bullets (each `li` a
fragment) and animation rests (`span.fragment anim-step`, Backend/Animation.agda:287).  The pages
step through every `.fragment` (`assets/plain.js`, reveal.js), but the model's
`ticks s = length (chunkL s)` (Deck/Syntax.agda:143) counts chunks only.  So `visible`, `deckM`,
`goto` and `render-events` are wrong for slides that use the other three (Intro, Talk and
Showcase do).  One fold of steps, with the deck a reindexing of it: planned (S4).

| Relation | Form | Section / retraction | Status |
|---|---|---|---|
| `Media → Timed` | model homomorphism | — | holds: `events-sample` (Scene/Sample.agda:340) |
| Plot ⊂ Diagram (meanings) | sub-object: `W × H` drawings, closed under overlay | inclusion / none | holds for the frame: `size-render` (Plot/Laws.agda:25); `Framed W H`: planned (S5); `render` a homomorphism: does not hold (clipping, rounding; legend and axes read all series) |
| Diagram ⊂ Animation | split mono | `pure` / `firstFrame`, `animationFinal` | holds pointwise: `diagram-const` (Scene/Animation.agda:83); the retraction law: planned, later (S2) |
| Animation ⊂ Program | sub-bialgebra | `inject` / `hd` | holds: `inject-const` (Program/Sem.agda:128); generic `sem-inject`: planned (S1) |
| Deck → Program | reindexing of the step stream along `runs navM zero` | none | holds by definition (Deck/Machine.agda:88); per slide: `pause-agree` (Deck/Program.agda:84); per deck: does not hold (needs preemption, **[decided]** out); step count: planned (S4); deck behaviour stated once: planned, later (S3) |
| Backend support → Program | reindexing along `mapMaybe dec` | none | holds: `lower-sound` (Program/Supports.agda:147) |
| Dia ⊂ Dia⁺ (syntax) | extension | `inject` / `lowerDia` (`lowerCurve`) | holds: `lower-inject` (Diagram/Curve/Properties.agda:17) |
| Scene ⊂ Program (syntax) | extension | `inject` / `skip` (`skipOp`) | holds: `skip-inject` (Program/Syntax.agda:56) |
| Dia ℕ ⊂ Plot content (syntax) | extension | `translate inl` / `lower (copairL ret renderMark)` | planned (S5) |
| any extension | split mono, one lemma | `translate inl` / `lower (copairL ret h)` | planned (S1), in `Container.Sum.Properties` |
| behaviours over a model | power model `O^(List C)` | — | planned, later (S2) |
| reading at the start | model homomorphism and retraction | constant sections / `firstFrame`, `now`, `hd` | planned, later (S2) |

## Where things live
- Containers: `Container.FreeMonad` (`pfold`; `All⋆ P t`, the predicate `P` on every command of
  `t`, used by `AllSup` and `SidesDia`), `.FreeMonad.{Algebraic,Properties}`, `Container.Lowering`
  (`.Properties`, `.Translate`, `.Category`), `Container.Sum` (`copairL`; `.Properties`),
  `Container.Tagged` (`over`), `Container.Polynomial`, `Container.Interpret.*`,
  `Container.Category`, `Container.Pick`.
- Scalars: `Slides.Scalar.{Core,Space,Time,Coupling,Hom}`; models `Slides.Scalar.Model.{Nat,Rat}`.
- Text and formulas: `Slides.Text` (`Inline`, runs), `Slides.Math` (`Math`, `toLaTeX`).
- Diagram: `Slides.Diagram.Syntax` (the signature), `.Draw` (`Layout`), `.Place` (`Placement`),
  `.Layout` (the fold), `.Laws` (`Action`, sizes), `.Assoc`, `.Valid`, `.Commute`, `.Overlay`,
  `.Names`, `.Natural`, `.Functoriality`, `.Print` (SVG), `.Convenience`; curves
  `Slides.Diagram.Curve` (`CurveC`, `Dia⁺`, `lowerCurve`).
- Scene: `Slides.Scene.Syntax`, `.Algebra` (`Payload`, `Temporal`), `.Events`, `.Sample`,
  `.Relation`, `.Equiv` (`_≈ₛ_`, Hudak's axioms), `.Tick`, `.Moving`, `.Animation` (`frameAt`,
  `diagram-const`).
- Program: `Slides.Program.Syntax` (`ProgC`, `inject`, `skip`), `.Sem` (`sem`, behaviours),
  `.Machine` (Moore machines), `.Navigation` (`navM`), `.Supports` (`lower-sound`).
- Deck: `Slides.Deck.Content` (`Block`, `Flow`), `.Syntax` (`Slide`, `ticks`, `flat`), `.Read`
  (`visible`), `.Machine` (`deckM`), `.Program` (`elab`, `pause-agree`), `.Clock`, `.Lower`
  (`FlowLowering`), `.DSL`, `.Anim`, `.Talk`.
- Plot: `Slides.Plot.Mark` (`Mark`, `MarkC`), `.Render` (`render`, `renderMark`), `.Laws`,
  `.Axis`, `.Ticks`, `.Log`, `.Clip`, `.Exact`, `.Anim`, `.Csv`.
- 3D: `Slides.Trig` (and `.Properties`), `Slides.Three.{Point,View,Solid,Render,Properties}`.
- Backends: `Slides.Backend.Render` (the shared core), `.Reveal`, `.Plain`, `.HTML`, `.Animation`
  (shipped events, `firstFrame`), `.Share` (sharing), `.Input` (bindings); the IO edge
  `Slides.Driver`.

## The objects
**Space, Time, Coupling** (three small theories; ℕ and ℚ are models; `ι : ℕ → ℚ` a model
homomorphism).  *Space*: lengths and positions, an ordered monoid with exact subtraction and
percentages; scaling by ratios is the optional `Scale`.  *Time*: instants and durations, an
ordered monoid with floor and the embedding of whole ticks (`tick`, a tick read as a length);
remainder is the optional `Time.Rem`.  *Coupling*: ratio of durations, easing, interpolation
between lengths.  Layout depends on Space only, sampling on Time and Coupling only.  Proofs use
the laws of the theory, never computation in ℚ; model facts (density, induction) are named
hypotheses.  **[decided]** Time is a parameter, ℚ the first model.  The ordered monoid `OrdMon`
is stdlib structures (`IsCommutativeMonoid`, `IsDecTotalOrder`, `Supremum` for the join), and a
model homomorphism `IsOrdMonHom` is an `IsMonoidHomomorphism` with an `IsOrderMonomorphism`.

**Text**: one tree of styled runs (text, code, emphasis, sub- and superscript, style, break,
math, link, citation) shared by prose and diagram labels.  Every consumer is a fold: HTML, plain
text (a monoid homomorphism to lines), SVG, width.

Formulas and runs are free monads of small signatures, a node of `n` sub-terms having positions
`Fin n`.  `Math = MathC ⋆ String` has identifiers as variables, so substitution is `>>=` and
`toLaTeX` is a handler; `latex` is congruent, so printing commutes with substitution
(`toLaTeX-bind`, an instance of `pfold-bind`).  `Inline = InlineC ⋆ ⊥` has leaf commands (text, code, break, math,
citation) and one wrapper command carrying a `Wrap` (emphasis, strong, sub, sup, style, link);
plain runs and HTML pieces are handlers read by `pfold`, width, `tspan`s and markup match the
root.  `wrap-runs`: a wrapper has the strings of its sub-runs.  `Block` stays a rose tree over
lists: `Flow` must remain a monoid under `++` as the leaf carrier of scenes, so deck lowerings
keep their own recursion (`FlowLowering`, `_⋙ᶠ_`, apart from `Container.Lowering`).  `glue`
is a monoid on `List⁺ Flow` (`glueMonoid`) and `chunks` an `IsMonoidHomomorphism` from `(List
Item, ++, [])`.  `Slides.Deck.Clock` instantiates events and sampling once for decks.

**Plot marks**: `Mark X Y` is a bifunctor in its coordinate types (`bimap`, `zipWith⁺`, with
`bimap-id`, `bimap-∘`), so `logMark = bimap id log₁₀` and `lerpMark t` is a zip; error bars are
stored by their ends (`bars`), exact in log space.  `MarkC = Mark ℚ ℚ ▷ λ _ → ⊥` is a signature
of arity-⊥ commands and `renderMark : Lowering MarkC (DiagramC ℕ)`; plot content stays a list of
series (legends, `reveal` and `morph` read the list).  `exact` samples with `Curve.curve`.

**Diagram**: the free algebra of the layout signature (primitives with intrinsic size;
connectives placing frames relative to each other) over a Space scalar.  Size is a derived
(synthesised) attribute, not stored.

The signature is a functor from scalars to containers: a command is a tag and a payload
(`Slides.Diagram.Syntax`), the arity depends on the tag only, and the payload's scalars are found
by structure (`fmap`).  A change of scalar is then a container morphism with the identity on
positions (`Container.Tagged.over`), `mapDia` is `translate` along it, and its functor laws are
`over-id`/`over-∘` from the laws of `fmap`, with no clause per command.

**Layout**: the carrier of the placement fold: a frame, the primitives at resolved positions,
named anchors.  Printers (SVG, others) are maps over its primitive list.  One drawing
vocabulary.  Layout is natural in the scalar.

Sizes are folds into envelope semigroups (Yorgey): beside into `(S,+)×(S,⊔)`, above into
`(S,⊔)×(S,+)`, atop into `(S,⊔)×(S,⊔)`, stdlib `CommutativeSemigroup`s by `DirectProduct`, so the
size laws are their laws (semigroups, not monoids: `OrdMon` has no `0 ≤ x`).  Translation is an
`Action` of `(S×S, ⊕)`, stated once, on drawings, anchors, lists and their product; a connective
is a `Placement` (frame and two offsets from the children's frames) given to `combine`, "act,
then concatenate", so associativity of `combine` and the name laws are single calculations.
`besideA`/`aboveA` are `IsSemigroup` per alignment, valid layouts form `Monoid`s with `empty`
(equal when their layouts are), and cutting a row or column is one lemma (`cut`).

**Scene** over leaves: the free algebra of a temporal signature (parallel overlay, windowing,
shifting, sequence, repetition, driving a leaf by a moving value) over those leaves, after
Hudak's temporal media.  Meaning: a sparse list of events (onset, duration, leaf in local
time), in which sequence and repetition are derived (a window and a shift under overlay); the
pointwise reading "time to maybe-leaf" is a fold of it, with relative windows and a shift
action so nested clocks are one law.  Both meanings are folds of one *temporal algebra*
(`Scene.Algebra`: a payload with none, par, clip, shift, drive; duration, sequence and repetition
derived), related by one logical relation (`Scene.Relation`).  Reading events is a monoid
homomorphism from `(List Event, ++, [])` to readings under pointwise overlay (`readE-hom`), and
scenes are equal in a setoid `_≈ₛ_` (equal durations, pointwise equal readings) in which the
signature is congruent and Hudak's axioms are equations (`Scene.Equiv`: `∥` associative,
commutative, absence its unit; `⨾` associative; delays add; `hold`, `delay`, `drive` distribute
over `∥`).  The unit of `⨾` holds only for windowed scenes and `hold a (hold b s)` is the narrow
window only for `a ≤ b`, since leaves are eternal and `hold` keeps its given duration.

The scene signature is `Tagged arity (λ t → Held t T D)`, as the Diagram one: a tag fixes the
arity, `Held t T D` the payload (a duration, a count, a driver, or nothing), the old constructor
names are pattern synonyms, and a change of clock and drivers `mapSC h g = over arity (mapP h g)`
has `mapScene-id`/`mapScene-∘` from `over-id`/`over-∘`.  `Held` is per tag rather than `Fields`
because the payload has two scalar kinds.
**[decided]** Interpolation is in scope: a moving value
is a term of Coupling, so no separate track datatype exists.  An *animation* is a scene of
diagrams with a time variable; a *deck* is a scene of scenes with content leaves
(**[decided]**); a pause is a one-tick delay.

**Program** over user commands: the free monad adding "wait for a command" to scenes.  Meaning:
a *behaviour* `List C → O`, the final Moore machine (a machine is a coalgebra of `X ↦ O × (C → X)`;
`obs` is its unique map into the behaviours, `final` the converse, bisimilar machines are exactly
those with equal traces).  Behaviours are compared pointwise, a setoid at level 0; `sem` is the
fold of the program signature into them.  Scene operations over waiting children are the
synchronous product (`prodB`: every child sees every command; **[decided]** true parallel
composition of programs is not supported); `await c` is blank until `c`, then runs the rest; a
scene is a program that never waits (`inject-const`: a constant behaviour).  A backend's lowering
is sound as `mapMaybe dec` on the commands (`lower-sound`).
A backend binds a subset of the commands.  Navigation state is machine state.  **[decided]**
The machine yields the *visible slide*; the accumulated view (chunks so far) is derived and
agrees with it for the pause fragment.

**Content**: flow content (text, lists, math, tables) laid out by the browser; a separate leaf
carrier sharing the temporal and input structure, not the geometry.  **[decided]** Slides are
leaves of a scene in sequence; labels are slide data, with a command that jumps to one; a pause
is a one-tick delay under overlay in a deck and a wait for `next` in its program.

## The maps that carry the weight
1. Lowerings between signatures (Kleisli maps of free monads; they compose).
2. Folds as homomorphisms: layout (natural in the scalar), events to the pointwise reading,
   the machine fold, text to its readings.
3. Embeddings with agreement: diagram as constant scene; deck as scene of scenes; program as
   scene (a fold).
4. Backends are algebras of the deck signature over one shared core; restyling is a
   homomorphism of backends.
5. Model homomorphisms between ℕ and ℚ, with lowerings where an operation is not preserved.

## Decisions
**Shipping to the page.**  The event list is JSON in a `script type="application/json"` child of
the animation (not an attribute: entity-escaped quotes tripled the size), with `< > &` written
as `\uXXXX`.  Diagrams and scalar terms of the events are trees; the shipped form is their finite
DAG (a table of nodes whose children are earlier positions; equal subtrees are one entry, an entry
used once is written in place).  `unshare` reads it back and `readBack (shareTop ts []) ≡ ts` is
proved (`Slides.Backend.Share.Properties`), as the stdlib bundle `sharing : List Tree ↪ (List Entry
× Tab)`; the table only grows at its new end (`Suffix _≡_`).  The trees are made by handlers:
`scI = pfold (spaceJ ⊕ timeJ) leafJ`, `drvI = pfold couplingJ leafJ`, `diaT = pfold diaJ`.
Hash-consing stays a fold over printed text: a generic one over `C ⋆ ⊥` would need decidable
equality on every payload.  The page resolves a reference when it is reached
(`assets/animation.js`, tested against Agda's frames by `make test-anim-ref`).  Loops and steps in
flight stand still while printing.

**Easing.**  A cubic Bézier is a constructor of the Coupling easing (`Bezier x₁ y₁ x₂ y₂`,
hundredths), evaluated in ℚ by sixteen bisection steps and clamped at the ends, so `ease-0` and
`ease-1` hold for it; the page evaluator has the same function.

**Loops and steps.**  Steps over a loop (`animateBoth`) is one scene: `n` phases, each the acts
in sequence, end to end; the loop picks the phase (real time modulo `n` ticks), the steps play
within it.  Phases of unequal length are rejected where the animation is written (`uniform?`, an
unsolved-meta check like `figure`).  A raw frame list is a scene of one-tick frames (`frames`,
`flipTween`); there is no frame-list content block.

**Lowering decks.**  Lowerings of the deck vocabulary are Kleisli maps `Block → Flow` lifted to
flows and talks (`Slides.Deck.Lower`): `lowerFlow` is a monoid homomorphism, lowerings compose
before they are lifted, a pause survives its content.

**Primitives.**  Scalar-parametric: `Ellipse rx ry` (frame 2rx by 2ry) and `Polyline closed pts`
(points from the frame's top-left; the frame is the extent of the points from the origin, so the
empty list is the empty frame; closed prints as a fillable `<polygon>`).  They move with scalars
(`mapOp`) and with animation terms, and are natural, valid and name-free like the others.
`Disc r` stays a primitive of the same size as `Ellipse r r` (`size-disc-ellipse`) because it
prints as `<circle>`.  Filled shapes that repeat (histogram columns, error bars, curves) are one
`Path`: opaque SVG path data in the frame's units, for shapes that are not a list of points; not
scalar-parametric, so it cannot move with the animation time.

**Convenience.**  `Slides.Diagram.Convenience` is the one home of the combinators decks repeat
(operators, gaps, rows and columns, margins, text, boxes, layers), each a one-line definition over
the core constructors; its laws are in `Convenience.Properties` (cutting a row or a column
anywhere, from `Diagram.Assoc`).

## Not supported
One single-sorted signature for everything; value-dependent switching (full FRP); parallel
composition of programs; opaque black-box frames; time domains beyond the Time theory.

## Open
Fade as a window or as an opacity scalar: both can exist.

## Literature
Hudak (temporal media); Elliott and Hudak, *Functional Reactive Animation*, ICFP 1997; Elliott,
*Push-pull FRP*, 2009; Yorgey, monoids and envelopes in diagrams; Henderson, functional
geometry; Abbott, Altenkirch, Ghani, *Containers*; Swierstra, *Data types à la carte*;
Hyland, Plotkin, Power, sums of effects; Plotkin and Power, algebraic operations; Hancock and
Setzer, interaction structures; Rutten, coalgebra (Moore machines); Henzinger, Manna, Pnueli,
*What good are digital clocks?*; Alur and Dill, timed automata.
