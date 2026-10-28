# The objects, and the maps between them

The one document every contributor and agent reads first.  Ideas and maps, not code names.
Decisions are marked **[decided]**; the rest are defaults to revisit only with a reason.

## Principles
- Nontrivial types are free algebras of a signature (free monads over containers) so that
  substitution is bind, folds are algebras, and relations between languages are
  injections, lowerings and homomorphisms.  Every type must say which of these it is.
- Identity and composition laws are proved where the structure is stated, once, generically
  (in `Container.*`), never re-proved per language.
- Meaning first (denotational design): fix the semantics, then show each implementation is a
  homomorphism of it.  Literature is the compass (below).
- No instance search in core.  `--safe --without-K`.  A new layer must delete or port more than
  it adds.

## The objects
**Space, Time, Coupling** (three small theories; ℕ and ℚ are models; `ι : ℕ → ℚ` a model
homomorphism).  *Space*: lengths and positions, an ordered module over the ratios.  *Time*:
instants and durations, an ordered monoid with floor and remainder and the embedding of whole
ticks.  *Coupling*: ratio of durations, easing, interpolation between lengths, a tick read as
a length.  Layout depends on Space only, sampling on Time and Coupling only.  Proofs use the
laws of the theory, never computation in ℚ; model facts (density, induction) are named
hypotheses.  **[decided]** Time is a parameter, ℚ the first model.

**Diagram**: the free algebra of the layout signature (primitives with intrinsic size;
connectives placing frames relative to each other) over a Space scalar.  Size is a derived
(synthesised) attribute, not stored.

**Layout**: the carrier of the placement fold: a frame, the primitives at resolved positions,
named anchors.  Printers (SVG, others) are maps over its primitive list.  One drawing
vocabulary (**[decided]**: merge the three legacy ones).  Layout is natural in the scalar.

**Scene** over leaves: the free algebra of a temporal signature (primitive: parallel overlay,
windowing, shifting, driving a leaf by a moving value; sequence and repetition are derived
forms, sequence being a window and a shift under overlay) over those leaves, after Hudak's
temporal media.  Meaning: a sparse list of events (onset, duration, leaf in local time);
the pointwise reading "time to maybe-leaf" is a fold of it, with relative windows and a shift
action so nested clocks are one law.  **[decided]** Interpolation is in scope: a moving
value is a term of Coupling, so no separate track datatype exists.  An *animation* is a scene
of diagrams with a time variable; a *deck* is a scene of scenes with content leaves
(**[decided]**); pause is a one-tick delay.

**Program** over user commands: the free monad adding "wait for a command" to scenes.  Meaning:
a Moore machine (state yields a scene reading, a command yields the next state); scene
operations over waiting children are the synchronous product of their machines (**[decided]**; true
parallel composition of programs is not supported); a scene is a
program that never waits.  A backend binds a subset of the commands.  Navigation state is
machine state.  **[decided]** The machine yields the *visible slide*; the accumulated view
(chunks so far) is derived and agrees with it for the pause fragment.

**Content**: flow content (text, lists, math, tables) laid out by the browser; a separate leaf
carrier sharing the temporal and input structure, not the geometry.

## The maps that carry the weight
1. Injections and lowerings between signatures (Kleisli maps of free monads; compose).
2. Folds as homomorphisms: layout (natural in the scalar), events to the pointwise reading,
   the machine fold.
3. Embeddings with agreement: diagram as constant scene; deck as scene of scenes; program as
   scene (a fold).
4. Backends are algebras of the deck signature over one shared core; restyling is a
   homomorphism of backends.
5. Model homomorphisms between ℕ and ℚ, with lowerings where an operation is not preserved.

## Shipping to the page  **[decided]**
Ship the event list with parametric leaves and a small evaluator generated from the scalar
signatures; do not port the legacy encoding stack.  Reintroduce shared subformulas only if a
measurement of page size demands it.

## Not supported
One single-sorted signature for everything; value-dependent switching (full FRP); parallel
composition of programs; opaque black-box frames; time domains beyond the Time theory.

## Open, defer until the step that needs it
Fade as a window or an opacity scalar (Step 4: both can exist).

**[decided, Step 5]** Deck: slides are leaves of a scene in sequence; labels are slide data, not
commands; a pause is a one-tick delay under overlay in a deck and a wait for `next` in its program.

## Literature
Hudak (temporal media); Elliott and Hudak, *Functional Reactive Animation*, ICFP 1997; Elliott,
*Push-pull FRP*, 2009; Yorgey, monoids and envelopes in diagrams; Henderson, functional
geometry; Abbott, Altenkirch, Ghani, *Containers*; Swierstra, *Data types à la carte*;
Hyland, Plotkin, Power, sums of effects; Plotkin and Power, algebraic operations; Hancock and
Setzer, interaction structures; Rutten, coalgebra (Moore machines); Henzinger, Manna, Pnueli,
*What good are digital clocks?*; Alur and Dill, timed automata.  Bibliographic checking status
is in `../agda-slides-legacy/docs/Time.md`.
