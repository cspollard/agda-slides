{-# OPTIONS --safe --without-K #-}

-- The curve extension: a function as a drawable, by sampling.
--
--   CurveC S    one primitive, `Function f lo hi style` (arity ⊥): the graph of `f : S → S` on [lo, hi]
--   Dia⁺ S      = (DiagramC S ⊎ CurveC S) ⋆ ⊥, the diagram language plus curves (Data types à la carte)
--   lowerCurve  Lowering (DiagramC S ⊎ CurveC S) (DiagramC S): `Function` becomes one Bézier `Path`
--
-- The function is the meaning and sampling is an implementation (Elliott, Functional Images), so
-- `Dia`, `Op` and every handler (layout, names, size, printing, animation shipping) are unchanged:
-- they run after `lowerDia`.  The curve is sampled at `n + 1` evenly spaced points and a monotone cubic
-- (Fritsch-Carlson, in the Fritsch-Butland form: the harmonic mean of neighbouring secants, zero
-- where they change sign, so no overshoot) is drawn through them, as one `Path` that is smooth on
-- every backend.  The `Path` is opaque: no morphing and no clipping inside it, and the frame is the
-- extent of the curve from the origin, like a `Polyline`.
--
-- `Dia⁺` is deliberately not functorial in `S`: `mapDia h` pushes a map of scalars through every
-- scalar of a term, but a `Function` is a *function* on scalars and `h : S → T` cannot be pushed
-- through `f : S → S` (no map back).  A change of scalar is done on `Dia`, after lowering.
--
-- Laws (generic ones are in `Container.Lowering.Properties`): `lowerDia` is a Kleisli extension, so
-- it preserves bind (`lower-bind`), composes (`lower-⋙`); `inject` followed by it is the identity
-- on `Dia` (`lower-inject`, in `Curve.Properties`).  `Within` is the ε-approximation contract, not proved.

module Slides.Diagram.Curve where

open import Level using (0ℓ)
open import Data.Bool using (Bool; if_then_else_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; map; zipWith; upTo; foldr; drop)
open import Data.Nat using (ℕ; suc)
open import Data.Product.Base using (_×_; _,_)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Container.Core using (Container; _▷_)
open import Data.Container.Combinator using (_⊎_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)

open import Container.Lowering using (Lowering; lower; translate)
open import Container.Sum using (inl)
open import Data.Sum.Base using (inj₁; inj₂)
open import Slides.Diagram.Style using (Style)
open import Slides.Diagram.Syntax using (Dia; DiagramC; Op; Path)

data Curve (S : Set) : Set where
  Function : (f : S → S) (lo hi : S) → Style → Curve S

CurveC : Set → Container 0ℓ 0ℓ
CurveC S = Curve S ▷ λ _ → ⊥

Dia⁺ : Set → Set
Dia⁺ S = (DiagramC S ⊎ CurveC S) ⋆ ⊥

function : ∀ {S} → (S → S) → S → S → Style → Dia⁺ S
function f lo hi s = impure (inj₂ (Function f lo hi s) , λ ())

-- a diagram is a diagram with curves (the embedding along `inl`)
inject : ∀ {S} → Dia S → Dia⁺ S
inject = translate inl

-- what sampling needs of the scalar: arithmetic (a total division), an order and a decimal
-- notation (`Slides.Plot.Exact` has the one for ℚ)
record Sampler (S : Set) : Set where
  infixl 7 _*_ _÷_
  infixl 6 _+_ _-_
  field
    fromℕ     : ℕ → S
    _+_ _-_ _*_ _÷_ : S → S → S
    _≤ᵇ_      : S → S → Bool
    show      : S → String

module _ {S : Set} (sm : Sampler S) where
  open Sampler sm

  -- `n + 1` evenly spaced values from `lo` to `hi`
  grid : ℕ → S → S → List S
  grid n lo hi = map (λ i → lo + ((hi - lo) * fromℕ i) ÷ fromℕ n) (upTo (suc n))

  -- the slope (per step) at each sample, from the differences `d` of neighbours: the ends take
  -- the one secant, an interior sample the harmonic mean of its two, or 0 where they disagree in sign
  slopes : List S → List S
  slopes []       = []
  slopes (d ∷ ds) = d ∷ go d ds
    where
      harmonic : S → S → S
      harmonic p q = if (p * q) ≤ᵇ fromℕ 0 then fromℕ 0 else ((fromℕ 2 * p) * q) ÷ (p + q)

      go : S → List S → List S
      go p []       = p ∷ []
      go p (q ∷ qs) = harmonic p q ∷ go q qs

  -- the Bézier pieces from point to point: control points a third of a step along the tangents
  pieces : S → List (S × S) → List S → String
  pieces third ((x₀ , y₀) ∷ t@((x₁ , y₁) ∷ _)) (m₀ ∷ ms@(m₁ ∷ _)) =
    "C" ++ˢ pt (x₀ + third) (y₀ + m₀ ÷ fromℕ 3) ++ˢ pt (x₁ - third) (y₁ - m₁ ÷ fromℕ 3) ++ˢ pt x₁ y₁
    ++ˢ pieces third t ms
    where pt = λ x y → show x ++ˢ " " ++ˢ show y ++ˢ " "
  pieces _ _ _ = ""

  -- the path through the samples of `f` on [lo, hi]; the frame is the extent from the origin
  curve : ℕ → (S → S) → S → S → Style → Op S
  curve n f lo hi s = Path hi (foldr top (fromℕ 0) ys) (start ps ++ˢ pieces third ps (slopes (zipWith _-_ (drop 1 ys) ys))) s
    where
      xs = grid n lo hi
      ys = map f xs
      ps = zipWith _,_ xs ys
      third = ((hi - lo) ÷ fromℕ n) ÷ fromℕ 3
      top = λ y m → if m ≤ᵇ y then y else m
      start : List (S × S) → String
      start []             = ""
      start ((x , y) ∷ _)  = "M" ++ˢ show x ++ˢ " " ++ˢ show y ++ˢ " "

-- the lowering: diagrams stay, a curve becomes its path
lowerCurve : ∀ {S} → Sampler S → ℕ → Lowering (DiagramC S ⊎ CurveC S) (DiagramC S)
lowerCurve sm n (inj₁ a)                        = impure (a , pure)
lowerCurve sm n (inj₂ (Function f lo hi s))     = impure (curve sm n f lo hi s , λ ())

lowerDia : ∀ {S} → Sampler S → ℕ → Dia⁺ S → Dia S
lowerDia sm n = lower (lowerCurve sm n)

-- The approximation contract (stated, not proved: it needs bounds on `f`).  `g` is the function the
-- drawn path denotes (the piecewise cubic through the samples), `dist` an absolute difference.
Within : ∀ {S} → (S → S → Set) → (S → S → S) → (g f : S → S) (lo hi ε : S) → Set
Within _≤_ dist g f lo hi ε = ∀ x → lo ≤ x → x ≤ hi → dist (g x) (f x) ≤ ε
