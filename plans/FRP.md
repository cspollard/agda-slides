# Continuous-time FRP, categorically

A short map of the category theory behind functional reactive programming, as a reference point
for our own semantics (`docs/Objects.md`, "How the objects relate").  Papers are in `lit/`
(gitignored; file names below).  Next steps: the maps between our semantics and this one, and
whether to implement any of it.

## 1. The denotation (Elliott and Hudak)

Time `T = ℝ`; for occurrences, `T̂ = T ∪ {−∞, +∞}`.

- `Behaviour A = T → A`: the power `A^T`.  Its `Functor`/`Applicative` structure is pointwise,
  so every algebraic law of `A` holds for behaviours (it is the power model).
- `Future A = T̂ × A`: the writer monad of the monoid `(T̂, max, −∞)`.
- `Event A`: a time-ordered list of occurrences `(T̂ × A)`, a monoid under merge.
- `switcher : Behaviour A → Event (Behaviour A) → Behaviour A`: at time `t`, follow the latest
  occurrence before `t`.  It is the bind of `Future`, used over and over.
- Denotational design: every operation is specified by its meaning, and the meaning function is
  a homomorphism of the structure (`Functor`, `Applicative`, `Monoid`, `Monad`).

Causality (the value at `t` depends only on what happened up to `t`) is a side condition here,
not something the types enforce.

`lit/Elliott-Hudak-1997-Functional-Reactive-Animation.pdf`, `lit/Elliott-2009-Push-Pull-FRP.pdf`,
`lit/Elliott-2009-Denotational-Design-TCM.pdf`.

## 2. Causality by construction: time-indexed sets

Take types to be presheaves over the time order, `Set^{(T, ≤)^op}`:
- a type is a family `A(t)`, "what is known by time `t`", with restriction to earlier times;
- a causal function is exactly a natural transformation, so causality comes from the category;
- the category is a topos, so it is cartesian closed: higher-order FRP for free.

Temporal operators become functors on it, and FRP types become LTL formulas (Jeffrey; Jeltsch):

| LTL | FRP | Structure |
|---|---|---|
| `□A` (always) | behaviour | comonad |
| `◇A` (eventually) | event (one occurrence) | monad; `□`-strong |
| `A U B` (until) | a behaviour, then a switch | `switch` is `◇`'s bind |

- **Discrete time** (`ω`): the topos of trees `Set^{ω^op}`.  It has a "later" modality `▷`, and
  every contractive map has a unique fixed point (guarded recursion).
  - `□A = νX. A × ▷X` and `◇A = νX. A + ▷X`, the delay monad (Capretta).
  - Cave et al. take `◇` as the least fixed point instead, so an event must fire (fairness).
  - Equivalently: causal stream functions, as coKleisli arrows of a history comonad
    (Uustalu and Vene).
  - Krishnaswami and Benton give an ultrametric model of the same idea; Krishnaswami (2013) and
    Simply RaTT (2019) make it space-leak free.
- **Continuous time** (`ℝ≥0`): there is no "next step", so no `▷` with unique fixed points.
  Recursion and `until` need care: Zeno behaviour, and the choice between strong and weak until.
  Jeltsch's abstract categorical semantics gives the structure a category must have to model
  temporal recursion and corecursion.

`lit/Jeltsch-2014-Categorical-Semantics-FRP-Temporal-Recursion.pdf`,
`lit/Birkedal-et-al-2012-Topos-of-Trees.pdf`, `lit/Capretta-2005-General-Recursion-Coinductive.pdf`,
`lit/Cave-Ferreira-Panangaden-Pientka-2014-Fair-Reactive.pdf`, `lit/Uustalu-Vene-2005-Signals-and-Comonads.pdf`,
`lit/Krishnaswami-2013-Higher-Order-FRP-Without-Leaks.pdf`, `lit/Bahr-Graulund-Mogelberg-2019-Simply-RaTT.pdf`.

## 3. Sheaves: continuous behaviour (Schultz and Spivak)

*Temporal Type Theory* uses sheaves on the interval domain (the topos `B`).
- A type is what can be observed over each time interval, with restriction to subintervals.
- The sheaf condition (gluing) says a behaviour over an interval is determined by its behaviour
  over any cover of it.  This replaces the "next step" of discrete time.
- Internal logic: properties holding over intervals; hybrid and continuous systems are its
  examples.  A continuous-time behaviour type is a sheaf here.

`lit/Schultz-Spivak-2017-Temporal-Type-Theory.pdf`.

## 4. Machines and composition (the discrete interactive layer)

- A Moore machine with inputs `C` and outputs `O` is a coalgebra of `X ↦ O × X^C`.  Its final
  coalgebra is `List C → O` (our `Semantics.Behaviour.final`).
- In polynomial functors it is a coalgebra of `Oy^C`, a lens `Sy^S → Oy^C`; machines are wired
  together in `Poly` (Niu and Spivak).
- Causal functions form a symmetric monoidal category with a delayed trace: feedback through a
  delay (Sprunger and Katsumata).
- Syntax into the final coalgebra by a fold is bialgebraic semantics: operations are given by a
  distributive law; GSOS rules for those that look one step ahead (Turi and Plotkin).
  Preemption (`until`) has a GSOS rule but is not an algebraic operation: it does not commute
  with bind.

`lit/Niu-Spivak-2024-Polynomial-Functors.pdf`, `lit/Sprunger-Katsumata-2019-Delayed-Trace.pdf`,
`lit/Turi-Plotkin-1997-Mathematical-Operational-Semantics.pdf`.

## 5. Where our semantics sits (to be worked out)

- `Timed` (a duration and a reading `ℚ → Maybe X`) is a behaviour of §1 on a bounded interval,
  with no input.  Scenes are Hudak's temporal media, a model of §1's `Behaviour` and `Event`
  fragment without switching.
- `Beh C O = List C → O` is §4, i.e. §2 in discrete time with the clock counting commands.
- Programs mean `List C → Timed`, and each command restarts the real-time reading.  The candidate
  bridge to §1: given timed commands `[(tᵢ, cᵢ)]`, at time `t` take the commands before `t`,
  their output, and read it at `t − t_last`.  That is a `switcher` whose event is the command
  stream, so it maps `Beh C Timed` into `Event C → Behaviour (Maybe X)`.  Done
  (`Semantics.FRP`, `Slides.Program.FRP`): causal, future-blind, a map of setoids, natural in the
  output.  Open: a homomorphism of the scene operations, which needs sorted events.
- Fran's animations are `Behaviour Image`.  Our animations are `Timed` over `Layout`, so the
  image side of that statement depends on a denotation of `Layout` as an image (`Slides.Diagram.Image`, generic in the
  primitive; `plans/Image.md` §4).

`lit/Elliott-2003-Functional-Images.pdf`, `lit/Porter-Duff-1984-Compositing.pdf`.

## Not downloaded

The links or hosts below were unreachable; fetch by DOI if needed.
- Jeffrey, *LTL types FRP*, PLPV 2012.
- Jeltsch, *Towards a common categorical semantics for LTL and FRP*, MFPS 2012 (ENTCS 286).
- Krishnaswami and Benton, *Ultrametric semantics of reactive programs*, LICS 2011,
  doi:10.1109/LICS.2011.38.
- Wan and Hudak, *FRP from first principles*, PLDI 2000, doi:10.1145/349299.349331.
- Uustalu and Vene, *The essence of dataflow programming*, APLAS 2005, doi:10.1007/11575467_2.
- Yorgey, *Monoids: theme and variations*, Haskell 2012, doi:10.1145/2364506.2364520.
- Henderson, *Functional geometry*, 2002.
