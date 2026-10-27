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
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (refl; sym)
open import Data.Bool using (T)

open import Slides.Diagram.Syntax using (Dia; spacer; mapDia)
open import Slides.Diagram.Expr using (Expr; evalWith; zero′)
open import Slides.Diagram.Euclid using (DExpr; evalD; natD)
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
--   * `template d` is an open diagram `d : Dia (Expr ⊤)`: its sizes are formulas in the
--     one variable `t` (`Slides.Diagram.Expr`), instantiated at a value of the
--     parameter by evaluating them in the scalar `S` with `t := fromℕ (units q)`.  A
--     template can be laid out once, symbolically, and shipped as formulas
--     (`Slides.Anim.Param`).  It needs no more than `Ops S`: `Expr` is the free
--     `Ops`-algebra, so there is exactly one way to evaluate it.
--
--   * `discrete d` is an open diagram `d : Dia (DExpr ⊤)` over the *Euclidean* signature
--     (`Slides.Diagram.Euclid`): floor division, remainder, comparison, a literal factor of
--     the tick.  Those operations have meaning in ℕ only, so the body is evaluated *in ℕ* at
--     the whole tick `units q` (`evalD natD`) and the numbers are then injected into the scalar
--     `S` (`fromℕ`).  So a discrete body has one frame per tick, and between two ticks it
--     shows the frame of the tick before (`units` rounds down): there is no interpolation,
--     and in ℚ (`ratOps`) the frame at time `q` is the frame of tick `⌊q⌋`.  It is shipped
--     symbolically like a template, as formulas read in ℕ (`Slides.Anim.DParam`); a `template`
--     and a `discrete` body can be played together (a template is a discrete one, read in ℕ,
--     `Slides.Diagram.Euclid.evalD-weaken`), but then the whole animation is discrete.
--
-- `bodyAt` is what every consumer of segments uses.
data SegBody (S : Set) : Set where
  blackBox : (ℚ → Dia S) → SegBody S
  template : Dia (Expr ⊤) → SegBody S
  discrete : Dia (DExpr ⊤) → SegBody S

bodyAt : ∀ {S} → Ops S → SegBody S → ℚ → Dia S
bodyAt O (blackBox f) q = f q
bodyAt O (template d) q = mapDia (evalWith O (λ _ → Ops.fromℕ O (units q))) d
bodyAt O (discrete d) q = mapDia (λ e → Ops.fromℕ O (evalD natD (λ _ → units q) e)) d

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
body : ∀ {S} → Ops S → Seg S → ℚ → Dia S
body O s = bodyAt O (content s)

ticks : ∀ {S} → Seg S → ℕ
ticks s = T.dur (track s)

-- An animation over leaves `T`
Anim : Set → Set → Set
Anim S T = AnimC ⋆ T

private
  pick2 : ∀ {A : Set} → A → A → Fin 2 → A
  pick2 a b zero          = a
  pick2 a b (suc zero)    = b
  pick2 a b (suc (suc ()))

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
tweenT : ∀ {S} → ℕ → ℚ → ℚ → T.Easing → Dia (Expr ⊤) → Anim S (Seg S)
tweenT n a b e d = pure (seg (pure (T.piece n a b e)) (template d))

-- the same, as a discrete template: the diagram is open in the integer tick `t`
tweenD : ∀ {S} → ℕ → ℚ → ℚ → T.Easing → Dia (DExpr ⊤) → Anim S (Seg S)
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
