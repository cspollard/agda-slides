{-# OPTIONS --safe --without-K #-}

-- The `exact` mark: a function drawn as a smooth curve.  `exactDia` composes the function with the
-- axis maps (frame pixels in ℚ), cuts the pixel range into the runs where the curve is inside the
-- box (clip before sampling: no smoothing across a cut), and draws each run with
-- `Slides.Diagram.Curve.curve` as one Bézier `Path` (a one-node diagram, in pixels).  Each run is sampled at `samples` points; the cut
-- is found on a one-pixel grid, so a run ends within a pixel of the edge.

module Slides.Plot.Exact where

open import Data.Bool using (Bool; _∧_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat as ℕ using (ℕ)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; _+_; _-_; _*_; _≤ᵇ_)

open import Data.Container.FreeMonad using (impure)
open import Slides.Diagram.Curve using (Sampler; curve)
open import Slides.Diagram.Style using (Style)
open import Slides.Diagram.Syntax using (Dia; mapDia)
open import Slides.Plot.Data using (inv; linspace)
open import Slides.Plot.Format using (trimmed)
open import Slides.Scalar.Model.Rat using (ι; ratFloor)

ratSampler : Sampler ℚ
ratSampler = record
  { fromℕ = ι ; _+_ = _+_ ; _-_ = _-_ ; _*_ = _*_ ; _÷_ = λ a b → a * inv b
  ; _≤ᵇ_ = _≤ᵇ_ ; show = trimmed 2 }

samples : ℕ
samples = 40

-- the maximal runs of consecutive points satisfying `ok`, as (first, last) with at least two
runs : (ℚ → Bool) → List ℚ → List (ℚ × ℚ)
runs ok = go
  where
    close : ℚ → ℚ → List (ℚ × ℚ)
    close a b = if b ≤ᵇ a then [] else (a , b) ∷ []

    mutual
      go : List ℚ → List (ℚ × ℚ)
      go []       = []
      go (x ∷ xs) = if ok x then run x x xs else go xs

      run : ℚ → ℚ → List ℚ → List (ℚ × ℚ)
      run a b []       = close a b
      run a b (x ∷ xs) = if ok x then run a x xs else close a b ++ go xs

-- the curve of `g` (frame pixels to frame pixels) over the pixels `x₀ … x₁`, whose values are
-- inside `y₀ … y₁`, in the style `s`, as a diagram
exactDia : (ℚ → ℚ) → (x₀ x₁ y₀ y₁ : ℚ) → ℕ → Style → List (Dia ℕ)
exactDia g x₀ x₁ y₀ y₁ n s =
  map (λ { (a , b) → mapDia ratFloor (impure (curve ratSampler samples g a b s , λ ())) })
      (runs (λ x → let y = g x in (y₀ ≤ᵇ y) ∧ (y ≤ᵇ y₁)) (linspace n x₀ x₁))
