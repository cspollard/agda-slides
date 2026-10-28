# Simplifying the library: a proposal for review

Status: proposal, not decided.  Sizes are estimates from reading the code
(`docs/Relations.md` is the evidence); nothing here was compiled.  This note is
about ideas and the maps between them, not about the current code's names.

## 1. Diagnosis

We added layers (time switch, ordered layer, decks as scenes) before fixing the objects
and the maps between them.  The same ideas are stated several times:

- the drawing primitives exist three times (in the syntax, in the layout result, and in
  the output record), and two of the types are misnamed;
- 275 to 375 lines of local proofs re-prove general facts about free monads, folds and
  lowerings that belong in the container library once;
- the two HTML backends share no code but share copied proofs;
- about 2.5k lines exist only to ship parametric encodings to a hand-written page
  evaluator;
- space and time are one scalar sort, which is why faithfulness conditions and
  case-by-case lowerings keep appearing.

## 2. The ideas we want to capture

**Space, time, and their coupling** (three small theories, not one scalar).
- *Space*: lengths and positions; an ordered module over the ratios (sum, maximum of
  frames, difference for centring, scaling by a ratio, comparison).  Nothing about ticks.
- *Time*: instants and durations; an ordered monoid with floor and remainder (for ticks,
  loops, hold) and the embedding of whole ticks.
- *Coupling*: the few operations that mix them: the ratio of two durations, easing of a
  ratio, interpolation between two lengths by a ratio, and reading a whole tick as a
  length.  This is where a moving value lives.
- Each is a Lawvere-style theory; ℕ and ℚ are models; a model homomorphism connects them.
  Layout depends on Space only; sampling depends on Time and the coupling only.  Space and
  time models are chosen independently.

**Diagram**: the free algebra of the layout signature (primitives with intrinsic size, and
connectives that place frames relative to each other) over a space scalar.  Not a tree of
transforms: placements are computed from sizes, as with envelopes (Yorgey) and functional
geometry (Henderson).

**Layout**: the carrier of the main fold on diagrams: a frame, the primitives at resolved
positions, and named anchors.  Other folds (declared names, what is touched) are further
algebras.  Choosing a concrete scalar is a model homomorphism, and layout is natural in it.

**Scene** over a type of leaves: the free algebra of a small temporal signature
(sequential composition, parallel overlay, windowing, shifting, repetition, and driving a
leaf by a track) over those leaves.  After Hudak's temporal media.  Its meaning is a
sparse list of events (onset, duration, leaf in local time); the pointwise reading
"time to maybe-layout" is a fold of that list.  Presence windows come from the events.
An animation is a scene of diagrams whose scalars mention a time variable: static
structure, varying values.

**Program** over a set of user commands: the free monad adding "wait for a command" to
scenes.  Its meaning is a Moore machine (state yields a scene, a command yields a next
state); a backend binds a subset of the commands.  A deck is a program whose scenes have
flow-content leaves and whose pause is a one-tick delay.

**Content** is a separate leaf carrier (text, lists, math, tables; laid out by the
browser), with its own semantics.  It shares the temporal and input structure, not the
geometry.

## 3. The maps that carry the weight (each stated once, generically)

1. Injections of one signature into a sum, and lowerings between signatures; both are
   Kleisli maps of free monads and compose.
2. Folds are algebra homomorphisms: layout natural in the scalar; events into the pointwise
   reading (with relative windows and a shift action, so nested clocks are one law);
   the machine fold.
3. Embeddings with agreement: a diagram as a constant scene; a deck as a scene of scenes;
   a program as a scene (a fold, since commands do not commute with continuation).
4. Backends are algebras of the deck signature over one shared core; restyling is a
   homomorphism of backends.
5. Model homomorphisms between ℕ and ℚ, one per sort, with lowerings where an operation is
   not preserved.

## 4. Proposed simplifications, safest first

1. **General lemmas, once** (pure deletion): the bind law for folds into monoids, and
   congruence for folds, in the container library; replace the local copies.
   About -275 to -375 lines.  No types change.
2. **Split the scalar** into Space, Time and Coupling; layout and sampling each depend on
   their own.  Spike first: does layout-naturality go through, and do discrete templates
   lower more simply?
3. **Names and one primitive vocabulary**: the free algebra is "Diagram"; the output record
   dissolves into "Layout"; the output primitives merge with the layout primitives.
4. **Events as the temporal semantics**; sampling, timelines and footprints become folds of
   it; the assembly theorem is stated on events.  Size not estimated.
5. **Shipping**: ship the event list with parametric leaves; generate the page evaluator
   from the scalar signatures; then delete the encoding stack piece by piece, keeping
   shared subformulas only if page size demands it (measure).
6. **Backends** share one deck algebra; they differ in lowering and shell.

## 5. What we choose not to support

- One single-sorted signature for everything (loses well-formedness; indexed containers
  would rewrite the library).  Specific languages related by injections instead.
- Value-dependent switching (full FRP), and parallel composition of programs.
- A generic time parameter beyond the Time theory and its models; opaque black-box frames.

## 6. Order and gates

Finish and merge the in-flight deck work (gates and docs outstanding), then 1 to 6.  Each
step is one agent on one branch and reports lines deleted, check time and memory against the
previous step, goldens unchanged unless explained, and the closure check.  A step that adds
more than it deletes stops and reports.

## 7. Decisions for the author

1. At deck level, should a machine's view be the accumulated content or the visible slide?
2. A fade: a presence window (in or out) or an opacity scalar?
3. Is a deck a scene of scenes (as spiked), with programs only for input?
4. Is interpolation (a track as a term) in scope now, or deferred?
5. How far on step 5 (a generated page evaluator is the largest, riskiest change)?
6. Is merging the three drawing vocabularies acceptable, given every example touches them?

## 8. Literature (from memory unless `docs/Time.md` marks it checked)

Hudak, temporal media; Elliott and Hudak, functional reactive animation; Yorgey, monoids
and envelopes in diagrams; Henderson, functional geometry; Hancock and Setzer, interaction
structures, and Rutten, coalgebra (Moore machines); Abbott, Altenkirch and Ghani,
containers; Hyland, Plotkin and Power, sums of effects; Henzinger, Manna and Pnueli, digital
clocks.
