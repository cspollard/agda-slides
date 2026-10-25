# Plan: animations

Goal (from `plan/TODO.md`): a DSL for animations in the style of `Dia` (a container,
its free monad, algebras), with a Reveal backend. Today animations are hand-written
JavaScript keyed by element ids (`assets/pairs/pairs.js`, see `docs/PairsDeck.md`).

## What the literature gives us

Read for this plan: Hudak, *An Algebraic Theory of Polymorphic Temporal Media*
(RR-1259, 2003; text extracted from the PDF, so quotes are approximate); Di Lavore and
Román, *Timing via Pinwheel Double Categories* (arXiv 2504.12846, read through an HTML
rendering); the PaSe paper (arXiv 2002.02171, HTML); reveal.js's auto-animate page.
Only abstracts of Hudak and Janin's *Tiled PTM* were available.

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
(`norm`, flattened to a parallel of `none · Prim · none` rows). Of these, the
commutativity of `:=:` will not hold for us: it needs a commutative `combineImage`,
and our `⊙` is z-ordered.

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

**Not used.** Continuous `Behavior = Time → a` (Fran) and Reanimate's `(Dur, Time →
SVG)`: the right target for video, wrong for a presentation, where the step is the
unit. They stay available as one more algebra (sampling).

## Design

### Syntax: `Slides.Anim.Syntax`

- `AnimC = Seq | Par`, both with `Fin 2` positions; `Anim T = AnimC ⋆ T`, with `T` the
  base media. `fmap`, `>>=`, `fold` come from `Container.FreeMonad` and
  `Container.Interpret`; nothing is re-proved.
- Base media `Frame S`: `hold d D`, the diagram `D : Dia S` shown for `d : ℕ` ticks.
  `none d = hold d empty`. Names (`named`) give elements identity across frames.
  A *flipbook* of diagrams reuses `Dia`, `Layout`, and the laws proved for `⊙`.
- Smart constructors derive the rest: `par a b` pads the shorter with `none`
  (computing `dur` by fold at construction), so well-formedness holds by construction;
  `a ⨾ b`, offsets, staggering (`sequence delay`, Motion Canvas's) are `Par` with
  pads; `tween` expands one primitive into k frames by `>>=`; `restyle`, `shift`
  are `fmap`.

### Algebras

| Carrier | Algebra | Role |
|---|---|---|
| `ℕ` | `dur`: `+`, `max`, `none d ↦ d` | well-formedness, padding |
| `List String` | `footprint`: names touched | disjointness for `Par` |
| `Timeline S = (ℕ , List (Layout S))` | `concat` = append, `merge` = frame-wise `⊙`, `zero d` = `d` empty layouts | the meaning (Hudak's `Combine`) |
| reveal markup | see below | the backend |
| sampling `Time → Layout S` | later | video, a continuous backend |

### Laws to prove (`Slides.Anim.Laws`)

For `Timeline`: associativity of `concat` and `merge`, units, additivity of `zero`, the
serial/parallel swap under equal durations, `dur` of the timeline equals `dur` of the
term. No commutativity (z-order). `fold` is a homomorphism by construction, so
these are laws of the algebra and hold for every term. Functor and monad laws and
fusion are the generic `Container.*` results. Completeness (normal forms) is a
stretch goal. Reversal as a fold with its involution by fusion is cheap and a good
first use of fusion.

### Reveal backend

Open: reveal.js offers two things and the repo should spike both, as it did for the
HTML printer (`Slides.Spike.Reveal`), before choosing.

1. **Auto-animate.** Each step is a section marked `data-auto-animate`; elements with
   the same `data-id` (taken from `named`) are interpolated, duration and easing by
   attributes. Needs an elaboration pass like `Slides.Steps`: a slide with an
   animation becomes a sequence of sections that repeat the rest of the content
   (matched, so static). *Risk:* the page documents matching of text, images and
   iframes; whether inline SVG children are interpolated is unverified.
2. **Fragments.** One slide, one SVG, step boundaries as fragment indices with CSS
   transitions on elements; reuses the existing `pause`/fragment machinery.
   *Risk:* generating per-step CSS for moves.

Plain HTML backend: show the final frame, or step through frames with its own script.

## Order

Each step ends with `make check`, `make test`, and the browser run.

1. **Spike.** A hand-written reveal page with an inline SVG, tried with auto-animate
   and with fragments; record what moves. Decide the backend strategy.
2. **Syntax and `dur`.** `AnimC`, `Anim`, smart constructors, `dur`, `par` with
   padding; an `Emacs` operator table in the docs.
3. **`Timeline` and laws.** The `Combine` instance and its eight laws; the swap law.
4. **Backend.** An `animate` command (a new stratum joined with `⊎`), the
   elaboration, golden and browser tests, and the Pairs deck's hand-written
   animation replaced by a described one as the first user.
5. **Extras.** `footprint`, reversal, `tween` by bind, a sampling algebra, easing.

## Decisions for the author

- **Time:** discrete ℕ ticks only, with sampling as an extra algebra (recommended), or
  continuous time from the start?
- **Base media:** whole-diagram frames (flipbook, recommended: reuses everything), or
  actions on named parts (`appear`, `move`, `restyle`), which are closer to what an
  author means but need a scene-state algebra and a conflict rule?
- **Commutativity of `Par`:** dropped (z-order). Acceptable?
- **Backend:** wait for the spike.
- **Tiled PTM** (overlap via synchronisation marks, an inverse monoid) would give
  staggered starts a proper algebra; read the full paper before deciding whether it
  replaces `Par` with padding.
