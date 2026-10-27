{-# OPTIONS --safe --without-K #-}

-- The animation language: temporal media after Hudak, as a free monad.
--
-- `AnimC` is the container of the two temporal connectives, `Seq` (one after the
-- other) and `Par` (together), each with two children.  Its leaves are
-- *segments*: a diagram shown for a whole number of ticks.  So
--
--     Anim S = AnimC ⋆ Seg S
--
-- `fmap` restyles every segment, `>>=` replaces a segment by an animation (a
-- tween is such a replacement), and `foldA` interprets a term in an algebra.
-- Durations are whole ticks because reveal advances in steps and a fractional
-- duration breaks `zero (a + b) = zero a ++ zero b` once sampled (Hudak).
--
-- `dur` is the first algebra: `Seq` adds, `Par` takes the maximum.  `par` is
-- well formed by construction: it pads the shorter side with an empty segment,
-- so both sides of every `Par` that the smart constructors build last equally
-- long.

module Slides.Anim.Syntax where

open import Level using (0ℓ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; _+_; _⊔_; _∸_; _<ᵇ_)
open import Data.Product using (_,_)
open import Data.Container.Core using (Container; _▷_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Container.Pick using (pick2)
open import Data.Bool using (true; false)
open import Data.Bool using (T)

open import Slides.Diagram.Syntax using (Dia; spacer; mapDia)
open import Data.Container.FreeMonad using (_>>=_)
open import Slides.Diagram.Ordered using (OExpr; OOps; evalO; lowerQ; holdT; zero′)
open import Data.Unit using (⊤)
open import Slides.Diagram.Scalar using (Ops)
import Slides.Anim.Track as T
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Integer as ℤ using ()

------------------------------------------------------------------------
-- The signature

data Op : Set where
  Seq Par : Op

AnimC : Container 0ℓ 0ℓ
AnimC = Op ▷ (λ _ → Fin 2)

-- a parameter as a whole number of the scalar's units (rounded down, negatives clamp)
units : ℚ → ℕ
units q = ℤ.∣ ℚ.⌊ q ⌋ ∣

-- The body of a segment: a diagram as a function of the parameter.
--
--   * `blackBox f` is any function `ℚ → Dia S`.  It can only be sampled (a flipbook).
--   * `template d` is an open diagram `d : Dia (OExpr ⊤)`: its sizes are formulas in the
--     one variable `t` (`Slides.Diagram.Ordered`: the layers both clocks read, so floor division,
--     remainder, comparison and a literal factor are there), instantiated at a value of the
--     parameter by evaluating them in the scalar `S` with `t := fromℕ (units q)`.  A template can be
--     laid out once, symbolically, and shipped as formulas (`Slides.Anim.Param`).  It needs no more
--     than an `OOps S`: `OExpr` is the free algebra, so there is exactly one way to evaluate it.
--
--   * `discrete d` is a template that is held between ticks: the formulas of `d` read the ℕ way
--     (`lowerQ`: the monus and the rounding percentage lowered to operations of both clocks) at the
--     whole tick `⌊t⌋` (`holdT`, `Slides.Diagram.Ordered.Properties.Laws.hold-law`).  So a discrete
--     body has one frame per tick and no interpolation; read in ℕ at the sample of a track it is
--     `d` itself (`Slides.Diagram.Ordered.Properties.Discrete.lower-ℕ`) and read in ℚ at a whole
--     tick it is `ι` of that (`discrete-is-ordered`).  It is not a second kind of body.
--
-- `bodyAt` is what every consumer of segments uses.
data SegBody (S : Set) : Set where
  blackBox : (ℚ → Dia S) → SegBody S
  template : Dia (OExpr ⊤) → SegBody S

discrete : ∀ {S} → Dia (OExpr ⊤) → SegBody S
discrete d = template (mapDia (λ e → lowerQ e >>= λ _ → holdT) d)

bodyAt : ∀ {S} → OOps S → SegBody S → ℚ → Dia S
bodyAt O (blackBox f) q = f q
bodyAt O (template d) q = mapDia (evalO O (λ _ → Ops.fromℕ (OOps.ops O) (units q))) d

-- A segment: a diagram that depends on a parameter, which follows a track for as
-- many ticks as the track lasts.  The track is explicit data (`Slides.Anim.Track`:
-- pieces with easings, steps for discontinuities); the body is the diagram as a
-- function of the parameter (`SegBody`), so reflow (a spacer that grows) and paint
-- (an opacity in a style) are both just uses of the parameter.  A diagram held for
-- `n` ticks is the constant track.
record Seg (S : Set) : Set where
  constructor seg
  field
    track   : T.Track ℚ
    content : SegBody S
open Seg public

-- the diagram at a value of the parameter
body : ∀ {S} → OOps S → Seg S → ℚ → Dia S
body O s = bodyAt O (content s)

ticks : ∀ {S} → Seg S → ℕ
ticks s = T.dur (track s)

-- An animation over leaves `T`
Anim : Set → Set → Set
Anim S T = AnimC ⋆ T

infixr 6 _⨾_
infixr 7 _∥ᵃ_

_⨾_ _∥ᵃ_ : ∀ {T} → AnimC ⋆ T → AnimC ⋆ T → AnimC ⋆ T
a ⨾ b  = impure (Seq , pick2 a b)
a ∥ᵃ b = impure (Par , pick2 a b)

-- A segment as a one-leaf animation
hold : ∀ {S} → ℕ → Dia S → Anim S (Seg S)
hold n d = pure (seg (pure (T.piece n 0ℚ 0ℚ T.Linear)) (blackBox (λ _ → d)))

-- a parameter moving from `a` to `b` in `n` ticks along an easing
tween : ∀ {S} → ℕ → ℚ → ℚ → T.Easing → (ℚ → Dia S) → Anim S (Seg S)
tween n a b e f = pure (seg (pure (T.piece n a b e)) (blackBox f))

-- the same, as a template: the diagram is open in the parameter `t`
tweenT : ∀ {S} → ℕ → ℚ → ℚ → T.Easing → Dia (OExpr ⊤) → Anim S (Seg S)
tweenT n a b e d = pure (seg (pure (T.piece n a b e)) (template d))

-- the same, as a discrete template: the diagram is open in the integer tick `t`
tweenD : ∀ {S} → ℕ → ℚ → ℚ → T.Easing → Dia (OExpr ⊤) → Anim S (Seg S)
tweenD n a b e d = pure (seg (pure (T.piece n a b e)) (discrete d))

-- a pause: an empty frame.  It is a template (constant, with the zero for its size), so
-- padding keeps an animation of templates parametric.
none : ∀ {S} → Ops S → ℕ → Anim S (Seg S)
none O n = pure (seg (pure (T.piece n 0ℚ 0ℚ T.Linear)) (template (spacer zero′ zero′)))

------------------------------------------------------------------------
-- Duration: the algebra into (ℕ, +, max)

-- fold of a program with leaves, into any carrier that has `Seq` and `Par`
foldA : ∀ {T A : Set} → (T → A) → (A → A → A) → (A → A → A) → AnimC ⋆ T → A
foldA leaf sq pr (pure t)              = leaf t
foldA leaf sq pr (impure (Seq , k))    = sq (foldA leaf sq pr (k zero)) (foldA leaf sq pr (k (suc zero)))
foldA leaf sq pr (impure (Par , k))    = pr (foldA leaf sq pr (k zero)) (foldA leaf sq pr (k (suc zero)))

dur : ∀ {S} → Anim S (Seg S) → ℕ
dur = foldA ticks _+_ _⊔_

------------------------------------------------------------------------
-- Well-formed parallel composition: pad the shorter side

-- extend to at least `n` ticks
pad : ∀ {S} → Ops S → ℕ → Anim S (Seg S) → Anim S (Seg S)
pad O n a with dur a <ᵇ n
... | true  = a ⨾ none O (n ∸ dur a)
... | false = a

-- both sides padded to the longer: a `Par` of equal durations
par : ∀ {S} → Ops S → Anim S (Seg S) → Anim S (Seg S) → Anim S (Seg S)
par O a b = pad O (dur b) a ∥ᵃ pad O (dur a) b
