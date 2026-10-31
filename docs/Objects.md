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
proved (`Slides.Backend.Share.Properties`); the page resolves a reference when it is reached
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
