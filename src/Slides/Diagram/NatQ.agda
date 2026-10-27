{-# OPTIONS --safe --without-K #-}

-- The naturals inside the rationals: `ι n = n/1`, which is `fromℕ` of `ratOps`.
--
-- Everything is proved through `ℚᵘ` (unreduced fractions), where the arithmetic computes:
-- `toℚᵘ (ι n) ≃ mkℚᵘ (+ n) 0`, and `toℚᵘ` is an injective homomorphism.  What is shown is
-- what the comparison of the discrete (ℕ) and the continuous (ℚ) frames needs
-- (`Slides.Anim.Continuous`): `ι` preserves `+`, `⊔`, `≤` (as a boolean) and the exact
-- case of `∸`, and `ι t · (1/d) = t/d`.

module Slides.Diagram.NatQ where

open import Data.Integer as ℤ using (+_)
open import Data.Nat as ℕ using (ℕ)
open import Data.Rational as ℚ using (ℚ; _/_)

ι : ℕ → ℚ
ι n = + n / 1
