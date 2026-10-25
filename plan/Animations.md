# Plan: animations

Goal (from `plan/TODO.md`): a DSL for animations in the style of `Dia` (a container,
its free monad, algebras), with a Reveal backend. Today animations are hand-written
JavaScript keyed by element ids (`assets/pairs/pairs.js`, see `docs/PairsDeck.md`).

## What the literature gives us

Read for this plan: Hudak, *An Algebraic Theory of Polymorphic Temporal Media*
(RR-1259, 2003; text extracted from the PDF, so quotes are approximate); Di Lavore and
Román, *Timing via Pinwheel Double Categories* (arXiv 2504.12846, read through an HTML
rendering); the PaSe paper (arXiv 2002.02171, HTML); reveal.js's auto-animate page.
Elliott's *Push-pull FRP* was read in full. Only the abstract of Hudak and Janin's
*Tiled PTM* was available.

**Hudak's `Media a` is a free monad.** `Media a = Prim a | m :+: m | m :=: m` is
`C ⋆ a` for the container `C` with two binary operations (`Seq`, `Par`), and the
variables are the *primitive* media. His `fmap` is the functor action (Thm 3.1), `foldM`
is our `fold` (with the `Prim` case as the environment), his fusion law (Thm 3.2) is
`Container.Interpret`'s fusion, and fold-map fusion (Cor. 3.3) is its naturality.
`reverse` is the fold `foldM (Prim . rev) (flip :+:) (:=:)`, and its involution is
proved by fusion (Thm 3.3). He uses `fmap` to avoid extra constructors (tempo, scale,
translate), and `>>=` would expand a primitive into a sub-animation. So, unlike
`Dia`, this is a case where the free monad's bind earns its keep: the leaves are
variables, not operations.

**Time.** `dur` is a fold into `(+, max)`, with `none d` (empty time of duration `d`)
as a primitive and the law `dur (none d) = d`. Hudak requires both sides of `:=:` to
have equal duration (well-formedness, his option 4) and gets the other three
meanings by inserting `none`. The meaning of a term is a homomorphism into a
`Combine` algebra `⟨I, concat, merge, zero⟩` (Thm 6.1); for animation `I` is a
duration with sampled frames. **His discretisation warning:** with a frame rate `r`,
`zero 1.06 ++ zero 1.06 ≠ zero 2.12`, so durations must be integral multiples of the
frame. That matches reveal's discrete steps, so durations should be ℕ ticks.

**Laws** (his Fig. 2): `:+:` and `:=:` are associative; `:=:` is commutative;
`none 0` is a unit of `:+:`; `none d` is a unit of `:=:` at `d = dur m`; `none` is
additive; and the *serial/parallel swap*
`(m1 :+: m2) :=: (m3 :+: m4) = (m1 :=: m3) :+: (m2 :=: m4)` when `dur m1 = dur m3` and
`dur m2 = dur m4`. Soundness is by the homomorphism; completeness is by normal forms
(`norm`, flattened to a parallel of `none · Prim · none` rows). Commutativity of `:=:` needs a commutative frame merge, and our `⊙` is z-ordered; see
"Commutativity of `Par`" below.

**Grading.** Di Lavore and Román grade morphisms by a *duoid*: two monoids on
durations, `+` for sequence and `max` for parallel, with only the lax interchange
`(a+b) max (c+d) ≤ (a max c) + (b max d)`; equality needs the durations to agree, and
the gap is closed by a `wait`. Their slogan is "processes in sequence share
resources; processes in parallel share time". My reading, not their claim: two
parallel animations must not touch the same part of the scene, so alongside `dur` a
`footprint` algebra (the names an animation touches) would say when `Par` is
well-formed. That answers PaSe's open question about conflicts.

**PaSe.** Its objection to monads is that bind can only be inspected up to the next
action, so analysis (duration) is lost. Fixed-arity containers avoid it: `Seq` and
`Par` have `Fin 2` positions, so `dur` and `footprint` are ordinary folds. It also
offers `relSequential` (start the second animation with an offset), which is `Par`
with a `none` pad.

**Push-pull FRP** (Elliott, Haskell '09, read in full). Semantics: a behavior is a
function of time and an event a list of timed occurrences; every instance
(`Functor`, `Applicative`, `Monad`, `Monoid`) is specified by making the semantic
function a *type class morphism*, i.e. the meaning of the composite is the
composite of the meanings. For us that is "the fold is an algebra homomorphism",
which is `Container.Interpret`. The paper also says that in Fran "discretization is
introduced automatically during rendering": sampling is the renderer's job, not the
program's. The original Fran paper is a scan and could not be read.

**Pomsets and concurrent Kleene algebra** (Gischer 1988; Hoare, Möller, Struth,
Wehrman 2009; Laurence and Struth's completeness result, from abstracts and talk
summaries only). Series-parallel partial orders have `;` and `∥` associative with
`∥` *commutative* (a pomset is unordered) and the exchange law
`(a ∥ b) ; (c ∥ d) ≤ (a ; c) ∥ (b ; d)` only as an inequality. Hudak's swap law is the
equality that holds once durations agree. **Duoidal categories** (Aguiar and Mahajan,
Booker and Street) are the categorical form: two monoidal structures and an
interchange map that need not be invertible; invertible interchange gives braided
monoidal categories. Di Lavore and Román's duoid grading is the same shape on
durations.

**Browser side.** reveal.js fragments take custom classes
(`.fragment.name` and `.fragment.name.visible`, with `data-fragment-index` for order),
and the Web Animations API takes keyframes with per-keyframe easing and interpolates
them (MDN). So a browser can do the continuous part itself, given keyframes, a
duration and an easing.

**Not used.** Continuous `Behavior = Time → a` (Fran) and Reanimate's `(Dur, Time →
SVG)` as the program's type: see "Time and backends" below.

## Time and backends

None of our backends can ask an animation for its value at an arbitrary time `t`: the
output is static markup and a stylesheet. Two consumers remain, and both are folds:

1. **Keyframes.** Emit the keyframes, a duration and an easing; the browser
   interpolates (CSS transitions, the Web Animations API, or reveal's auto-animate).
   The continuous part is the browser's.
2. **Sampling.** Evaluate the animation at ticks `0, 1, …, n` ourselves, at render
   time, as Fran's renderer does. That is Hudak's `Rendering = (Dur, [Image])` and is
   what an export to frames or video needs.

So a continuous-time *semantics* (`Time → Layout`) is optional. It would be the
specification that a `tween` primitive's keyframe-and-easing form approximates, and
the thing a sampler samples. Program time is ℕ ticks, a `tween` carries an easing as
data, and no backend needs a runtime that evaluates a Haskell-style function of
time. On-demand sampling at run time would need Agda to emit JavaScript functions,
which this library has no AST for.

## Commutativity of `Par`

If equality is taken up to reordering, `Par` is commutative as soon as the frame
merge is, and the merge is `⊙`. The geometry of `⊙` is symmetric (centring gives
offsets `W - wa` and `W - wb`, and `⊔` is commutative), so `atop a b` and `atop b a`
differ only in the order of the lists of drawing commands and anchors. Stdlib's
`Permutation` relations make that an equivalence. This is what pomsets do (a pomset
is unordered, so `∥` is commutative by construction). Three caveats:

- **Overlap.** Equality up to reordering identifies two pictures that differ when
  parts overlap, because the painter's order decides what is on top. So it is a
  coarser notion than "renders the same". Two ways out: give each drawing command a
  layer number and sort on it (Reanimate's z-index), which makes the merge commutative
  on the nose; or require `Par` operands to have disjoint footprints and not overlap.
- **Anchors.** `findAnchor` takes the first match, so reordering anchors changes which
  box a duplicated name finds. Equality up to reordering is a congruence for `connect`
  only if names are unique; `Names` would need to report duplicates.
- **Cost.** `Layout` equality moves from `Pointwise` to a permutation relation, and
  `Laws` needs a permutation version of `assoc3`, the unit lemmas and
  the swap law. Not yet proved; I expect it to be routine.

## Design

### Syntax: `Slides.Anim.Syntax`

- `AnimC = Seq | Par`, both with `Fin 2` positions; `Anim T = AnimC ⋆ T`, with `T` the
  base media. `fmap`, `>>=`, `fold` come from `Container.FreeMonad` and
  `Container.Interpret`; nothing is re-proved.
- Base media `Seg`: a duration `d : ℕ` (ticks) and a diagram `D : Dia S` shown for that
  long, with time-dependence in *paint tracks* (next section) and in tweens between
  frames. `hold d D` is the constant segment and `none d = hold d empty`. A flipbook of
  diagrams reuses `Dia`, `Layout`, and the laws proved for `⊙`.
- Smart constructors derive the rest: `par a b` pads the shorter with `none`
  (computing `dur` by fold at construction), so well-formedness holds by construction;
  `a ⨾ b`, offsets, staggering (`sequence delay`, Motion Canvas's) are `Par` with
  pads; `tween` between two frames expands by `>>=`; `restyle`, `shift` are `fmap`.

## Time dependence: paint tracks

Quantities split into **reflow** quantities (sizes, gaps, margins: they feed `⊔` in layout,
so a symbolic polynomial or Bézier scalar would leave the class of functions layout is
closed under, since a max of polynomials is piecewise with irrational breakpoints) and
**paint** quantities (translation, scale, rotation, opacity, colour, visibility: applied
after layout, never fed back). Paint quantities are explicit data:

```
Track A  = list of segments  (duration d, from v₀, to v₁, easing)
Easing   = Linear | Bezier x₁ y₁ x₂ y₂ | Step
```

- **Linear** is `v₀ + p·(v₁ - v₀)` with `p` the progress in `[0, 1]`. It is exact over
  ℚ (`percentOf`), so sampling and the laws are exact.
- **Bezier** is CSS's `cubic-bezier` timing function. Backends take it as data
  (`transition-timing-function`, SMIL `keySplines`). A sampler has to invert
  `x(s) = p`, a cubic with no exact rational root, so it uses a fixed number of
  bisection steps with a stated tolerance. Laws are stated for `Linear` and `Step`;
  `Bezier` sampling is an approximation, said so in its docstring.
- **Step** is the explicit discontinuity: hold `v₀` until the end of the segment, then
  `v₁` (CSS `steps(1, jump-end)`, SMIL `calcMode="discrete"`). A track whose
  consecutive segments do not meet (`v₁` of one `≠ v₀` of the next) is a jump at the
  boundary too. Values of a type that cannot be interpolated (visibility, a class name,
  an unlerpable colour) use `Step` only; the sampler is given the interpolation as an
  argument (`Lerp A`, with no instance search).
- **Semantics.** Segments are half-open `[tᵢ, tᵢ₊₁)`, so evaluation is total and
  right-continuous: at a boundary the *new* segment's start value holds, and the last
  segment's end value is the value at its end time. `eval (a ++ b) t = if t < dur a
  then eval a t else eval b (t - dur a)`, by induction on the segment list.

Tracks attach as unary annotation operations: `Move dx dy`, `Scale`, `Rotate`, `Fade`,
`Recolour`, `Show`, each taking tracks. They do not change a layout's size or anchors,
so the size algebra ignores them and the proofs are `Named`'s. They compose by *nesting*
(`Move a (Move b d)` is two groups), so tracks are never added to each other and no
closure is needed. Reflowing changes (a box growing and pushing its neighbours) are a
`tween` between two frames: layout is exact at each, and a browser interpolates matched
elements linearly between them (exact for translation and fade, an approximation where
`⊔` makes layout non-affine in between).

### Algebras

| Carrier | Algebra | Role |
|---|---|---|
| `ℕ` | `dur`: `+`, `max`, `none d ↦ d` | well-formedness, padding |
| `List String` | `footprint`: names touched | disjointness of `Par` operands |
| `Timeline S = Σ n. Vec (Layout S) n` | `concat` = append, `merge` = frame-wise `⊙`, `zero d` = `d` empty layouts | the meaning (Hudak's `Combine`) |
| `Σ n. (Fin n → Diagram)` | `compile` of each frame | what backends consume |

The backend interface is `Fin n → Diagram` (a frame per tick). The carrier is a `Vec`
and the function is its `lookup`: `Vec` has a decidable structure and needs no
function extensionality for the laws, and the two are isomorphic.

### Laws to prove (`Slides.Anim.Laws`)

For `Timeline`: associativity of `concat` and `merge`, units, additivity of `zero`, the
serial/parallel swap under equal durations, `dur` of the timeline equals `dur` of the
term, and commutativity of `merge` up to the permutation relation `≈ᵖ` (below).
`fold` is a homomorphism by construction, so these are laws of the algebra and hold
for every term. Functor and monad laws and fusion are the generic `Container.*`
results. Completeness (normal forms) is a stretch goal. Reversal as a fold with its
involution by fusion is cheap and a good first use of fusion.

## Backends: from `Fin n → Diagram`

Yes, SVGs animate this way, in two forms. Both consume the same `Fin n → Diagram`.

1. **Flipbook.** Emit all `n` frames as `<g>` groups inside one `<svg>` and show one at
   a time (class toggled by a few lines of script on fragment events). Works in every
   backend, including plain HTML and any later PDF or video export. Costs: markup
   grows with `n`, there is no easing, and it is only as smooth as the tick rate.
2. **Tracks (reveal).** Treat the frames as *keyframes*. Match elements across frames
   by `Style.ident` (the existing hook, set with `withId`); emit each matched element
   once, at its first position, and per step a CSS rule with `transform: translate(…)`,
   `opacity`, and colour, with a `transition` giving duration and easing. A few lines of
   script copy reveal's fragment state to a `data-step` attribute on the `<svg>`, so
   stepping backwards plays the transition in reverse for free (SMIL animations would
   need explicit reversal). Elements present in only some frames get opacity 0 outside
   them. Unnamed elements must be equal in all frames; `trackable` (a fold) checks that
   and the backend falls back to the flipbook otherwise.

"Curves parametric in time" are, in browser terms, the easing curve (`cubic-bezier`,
which CSS and SMIL's `keySplines` both take) applied between keyframes. That is the
better way where it applies: markup stays small, interpolation is hardware-accelerated,
and the program stays discrete. A parametric *path* (moving along a curve) is
`offset-path` or SMIL `animateMotion`, and is out of scope until a deck needs it.
Dense sampling is then just a `tween` that expands to many frames. Interpolating
a layout needs only `percentOf` from `Ops` (`a + percentOf p (b - a)`), so ℚ makes it
exact.

Risks to settle in the spike: CSS `transform` on SVG children (works, but check
`transform-box`/`transform-origin`), and reveal fragment events for a diagram that is not
itself a fragment.

## Order

Each step ends with `make check`, `make test`, and the browser run.

1. **Spike.** A hand-written reveal page: an inline SVG with three frames, driven by
   fragment events, as a flipbook and as tracks (CSS transitions), forward and
   backward. Record what works in reveal and plain HTML.
2. **Syntax and `dur`.** `AnimC`, `Anim`, smart constructors, `dur`, `par` with
   padding; an operator table with Emacs input sequences in the docs.
3. **`Timeline` and laws.** The `Combine` instance and its laws; the swap law;
   `≈ᵖ` and commutativity.
4. **Backend.** An `animate` command (a new stratum joined with `⊎`), flipbook first,
   then tracks; golden and browser tests; the Pairs deck's hand-written animation
   replaced by a described one as the first user.
5. **Tracks.** `Track`, `Easing`, `eval` and its laws, the paint annotations with
   their size-neutrality proofs, the CSS/SMIL emitter, then `footprint` checks,
   reversal, `tween` by bind, `trackable`.

## Proposal for the open questions

1. **Time.** ℕ ticks in the program. Backends take `Fin n → Diagram`; interpolation is
   the browser's (tracks) or ours (a `tween` that expands to frames). No continuous
   specification for now.
2. **Base media.** Whole-diagram frames with paint tracks (`Move`, `Fade`, … carrying
   `Linear`, `Bezier` or `Step` segments); reflow by tweening frames. Polynomial or
   Bézier *scalars* in layout are out: `⊔` leaves the class. A scene-state algebra for
   `appear`/`move` can be derived on top.
3. **Overlap and commutativity.**
   - `Par` requires its operands' footprints to be disjoint, checked by a decidable
     predicate that a deck asserts with `refl`, as it does for `dangling` (an
     ill-formed `Par` fails to typecheck).
   - Commutativity is stated up to `≈ᵖ`, equality up to permutation of draws and of
     anchors. Disjoint footprints make the anchor caveat vanish: no name is shared,
     so `findAnchor` is unaffected by the order.
   - Paint order *inside* a part is untouched; authors who need an ordered overlay use
     `⊙` within a frame. `Par` is for independent parts, and `≈ᵖ` is then the
     right notion. No layer numbers.
4. **Backend.** Flipbook first (it works everywhere), then tracks for reveal, as in
   "Backends".
5. **Tiled PTM.** Defer. Staggered starts are `Par` with a `none` pad until a deck
   needs overlap that padding cannot say; read the full paper then (the HAL pages are
   behind a bot check, so it needs a PDF from the author).
