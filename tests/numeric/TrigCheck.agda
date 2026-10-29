{-# OPTIONS --safe --without-K #-}

-- Closed numeric checks of `Slides.Trig`, kept off the normal typechecking path (ℚ equality by
-- `refl` normalises slowly): `make test-numeric`.  The order-5 polynomials against exact values of
-- sin and cos, within their bound of 3·10⁻⁴ (here 1/3000), and the exact folds of the circle.
-- Literals are written `mkℚᵘ n d`, meaning (n)/(d + 1), so nothing is divided.

module TrigCheck where

open import Data.Bool using (Bool; true)
open import Data.Integer using (+_; -[1+_])
open import Data.Rational.Unnormalised using (ℚᵘ; mkℚᵘ; _-_; ∣_∣; _≤ᵇ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Slides.Trig

close : ℚᵘ → ℚᵘ → Bool
close a b = ∣ a - b ∣ ≤ᵇ mkℚᵘ (+ 1) 2999

-- sin 30° = 1/2, cos 60° = 1/2, sin 45° = cos 45° ≈ 0.70711 (= 70711/100000)
_ : close (sin 5 (mkℚᵘ (+ 1) 11)) (mkℚᵘ (+ 1) 1) ≡ true
_ = refl
_ : close (cos 5 (mkℚᵘ (+ 1) 5)) (mkℚᵘ (+ 1) 1) ≡ true
_ = refl
_ : close (sin 5 (mkℚᵘ (+ 1) 7)) (mkℚᵘ (+ 70711) 99999) ≡ true
_ = refl
_ : close (cos 5 (mkℚᵘ (+ 1) 7)) (mkℚᵘ (+ 70711) 99999) ≡ true
_ = refl

-- the fold is exact: a quarter turn, a half turn and a negative angle (sin (−30°) = −1/2)
_ : close (sin 5 (mkℚᵘ (+ 1) 3)) (mkℚᵘ (+ 1) 0) ≡ true
_ = refl
_ : close (cos 5 (mkℚᵘ (+ 1) 1)) (mkℚᵘ -[1+ 0 ] 0) ≡ true
_ = refl
_ : close (sin 5 (mkℚᵘ -[1+ 0 ] 11)) (mkℚᵘ -[1+ 0 ] 1) ≡ true
_ = refl
