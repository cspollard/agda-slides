{-# OPTIONS --safe --without-K #-}

-- Writing data: decimals, a safe reciprocal, evenly spaced samples and the graph of a function.

module Slides.Plot.Data where

open import Data.Integer using (ℤ; +_)
open import Data.List using (List; map; upTo)
open import Data.Nat as ℕ using (ℕ; zero; suc; _∸_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_; ≢-nonZero; fromℚᵘ)
import Data.Rational.Properties as ℚP
open import Data.Rational.Unnormalised using (mkℚᵘ)
open import Relation.Nullary using (yes; no)

open import Slides.Scalar.Model.Rat using (ι)

private
  pow10 : ℕ → ℕ
  pow10 zero    = 1
  pow10 (suc k) = 10 ℕ.* pow10 k

-- `decimal m k` is m / 10ᵏ: `decimal (+ 125) 2` is 1.25
decimal : ℤ → ℕ → ℚ
decimal m k = fromℚᵘ (mkℚᵘ m (pow10 k ∸ 1))

-- the reciprocal, with 0 for 0
inv : ℚ → ℚ
inv q with q ℚP.≟ 0ℚ
... | yes _  = 0ℚ
... | no  ne = ℚ.1/_ q {{≢-nonZero ne}}

-- `n + 1` evenly spaced values from `lo` to `hi`
linspace : ℕ → ℚ → ℚ → List ℚ
linspace n lo hi = map (λ i → lo + (hi - lo) * ι i * inv (ι n)) (upTo (suc n))

-- the graph of a function at the given abscissae
graph : (ℚ → ℚ) → List ℚ → List (ℚ × ℚ)
graph f = map (λ x → x , f x)
