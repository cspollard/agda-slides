{-# OPTIONS --safe --without-K #-}

-- The animation language: temporal media after Hudak, as a free monad over one temporal container.
--
-- `TimeC` has the connectives `Seq` (one after the other) and `Par` (together), the unary
-- operations `Hold n` (shown for `n` ticks and not otherwise), `Delay n` (starts `n` ticks later),
-- `Repeat n` (`n` copies end to end) and `Drive tr` (binds the parameter of the templates below it
-- to the track `tr` at the local time: substitution along a signal, the `Track` is explicit data).
-- Leaves are templates, diagrams open in one variable (`Slides.Diagram.Ordered`), eternal until a
-- `Hold` gives them a window:
--
--     Anim = TimeC ⋆ Tmpl         seg tr d = Hold (dur tr) (Drive tr (pure d))
--
-- A segment is that derived form, not a leaf type.  `fmap` restyles templates, `>>=` replaces a
-- template by an animation, and `foldS` interprets a term in an algebra of `TimeC`.  Durations are
-- whole ticks (reveal advances in steps).  Absence is a unit of `Par` (`Slides.Time.mergeM`), so no
-- padding is needed: a gap is `Delay k (Hold 0 _)`.
--
-- `dur` is the first algebra: `Seq` and `Delay` add, `Par` takes the maximum, `Hold n` is `n`.  The
-- readings are `Slides.Anim.Sample` (parametric in the clock) and, for the ℕ clock, `Timeline`.

module Slides.Anim.Syntax where

open import Level using (0ℓ)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Nat using (ℕ; _+_; _*_; _⊔_)
open import Data.Product using (_,_; proj₂)
open import Data.List using (List; foldr; applyUpTo)
open import Data.Container.Core using (Container; _▷_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
open import Container.Pick using (pick2)
open import Data.Unit using (⊤)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Integer as ℤ using ()

open import Slides.Diagram.Syntax using (Dia; spacer; mapDia)
open import Slides.Diagram.Ordered using (OExpr; lowerQ; holdT; zero′; lit)
import Slides.Anim.Track as T

------------------------------------------------------------------------
-- The signature

data TOp : Set where
  Seq Par : TOp
  Hold Delay Repeat : ℕ → TOp
  Drive : T.Track ℚ → TOp

tarity : TOp → Set
tarity Seq        = Fin 2
tarity Par        = Fin 2
tarity (Hold _)   = ⊤
tarity (Delay _)  = ⊤
tarity (Repeat _) = ⊤
tarity (Drive _)  = ⊤

TimeC : Container 0ℓ 0ℓ
TimeC = TOp ▷ tarity

Scene : Set → Set
Scene A = TimeC ⋆ A

-- a template: a diagram whose sizes are formulas in the one variable `t`, the parameter
Tmpl : Set
Tmpl = Dia (OExpr ⊤)

Anim : Set
Anim = Scene Tmpl

-- a parameter as a whole number of the scalar's units (rounded down, negatives clamp)
units : ℚ → ℕ
units q = ℤ.∣ ℚ.⌊ q ⌋ ∣

-- a discrete template: held between ticks, read the ℕ way (`Slides.Diagram.Ordered`: `lowerQ`, `holdT`)
discrete : Tmpl → Tmpl
discrete = mapDia (λ e → lowerQ e >>= λ _ → holdT)

------------------------------------------------------------------------
-- Constructors

infixr 6 _⨾_
infixr 7 _∥ᵃ_

_⨾_ _∥ᵃ_ : ∀ {A} → Scene A → Scene A → Scene A
a ⨾ b  = impure (Seq , pick2 a b)
a ∥ᵃ b = impure (Par , pick2 a b)

hold′ delay repeat : ∀ {A} → ℕ → Scene A → Scene A
hold′ n a  = impure (Hold n , λ _ → a)
delay n a  = impure (Delay n , λ _ → a)
repeat n a = impure (Repeat n , λ _ → a)

drive : ∀ {A} → T.Track ℚ → Scene A → Scene A
drive tr a = impure (Drive tr , λ _ → a)

-- a segment: the template follows the track for as many ticks as the track lasts
seg : T.Track ℚ → Tmpl → Anim
seg tr d = hold′ (T.dur tr) (drive tr (pure d))

-- a diagram held for `n` ticks (the constant track)
hold : ℕ → Dia ℕ → Anim
hold n d = seg (pure (T.piece n 0ℚ 0ℚ T.Linear)) (mapDia lit d)

-- a parameter moving from `a` to `b` in `n` ticks along an easing, the template open in it
tweenT : ℕ → ℚ → ℚ → T.Easing → Tmpl → Anim
tweenT n a b e d = seg (pure (T.piece n a b e)) d

-- the same, as a discrete template: the diagram is open in the integer tick `t`
tweenD : ℕ → ℚ → ℚ → T.Easing → Tmpl → Anim
tweenD n a b e d = tweenT n a b e (discrete d)

-- A flipbook is a lowering target, not syntax: frames held one tick each.  `flipTrack tr f` samples
-- the parameter of `tr` at each tick and shows the diagram `f` of it (an arbitrary function: what
-- no template can say).  Its tracks are constant, so it has no parametric encoding.
flipbook : List (Dia ℕ) → Anim
flipbook = foldr (λ d a → hold 1 d ⨾ a) (hold′ 0 (pure (spacer zero′ zero′)))

flipTrack : T.Track ℚ → (ℚ → Dia ℕ) → Anim
flipTrack tr f = flipbook (applyUpTo (λ k → f (proj₂ (T.sample T.ℚLerp tr) k)) (T.dur tr))

flipTween : ℕ → ℚ → ℚ → T.Easing → (ℚ → Dia ℕ) → Anim
flipTween n a b e = flipTrack (pure (T.piece n a b e))

-- a gap: `n` ticks in which nothing is shown (absence is the unit of `Par`)
gap : ℕ → Anim
gap n = delay n (hold′ 0 (pure (spacer zero′ zero′)))

------------------------------------------------------------------------
-- Folds, and duration: the algebra into (ℕ, +, max)

foldS : ∀ {A X : Set} → (A → X) → ((s : TOp) → (tarity s → X) → X) → Scene A → X
foldS leaf alg (pure a)         = leaf a
foldS leaf alg (impure (s , k)) = alg s (λ p → foldS leaf alg (k p))

durAlg : (s : TOp) → (tarity s → ℕ) → ℕ
durAlg Seq        k = k fz + k (fs fz)
durAlg Par        k = k fz ⊔ k (fs fz)
durAlg (Hold n)   k = n
durAlg (Delay n)  k = n + k _
durAlg (Repeat n) k = n * k _
durAlg (Drive _)  k = k _

-- leaves are eternal: duration 0
dur : ∀ {A} → Scene A → ℕ
dur = foldS (λ _ → 0) durAlg
