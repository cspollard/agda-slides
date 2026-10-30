{-# OPTIONS --safe --without-K #-}

-- Ticks over ℚ: a "nice" step (1, 2 or 5 times a power of ten), and the multiples of it that fall
-- in the range, as the progression of `Slides.Plot.Ticks`.
--
-- `niceStep n span` is the smallest nice step for which `n` steps cover `span` (the largest
-- candidate, 5·10⁶, when none does; the smallest is 10⁻⁴).  The ticks are `k · step` for the
-- integers `k` with `lo ≤ k · step ≤ hi`, from the least `k = ⌈lo / step⌉` to the greatest
-- `⌊hi / step⌋`; a step is a ratio of whole numbers, so dividing by it is multiplying by the
-- ratio the other way up.

module Slides.Plot.Ticks.Rat where

open import Data.Integer as ℤ using (ℤ; +_)
open import Data.List using (List; []; _∷_; _++_; map; concatMap; upTo)
open import Data.Nat as ℕ using (ℕ; zero; suc; _∸_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _-_; _≤ᵇ_; fromℚᵘ; floor; ceiling)
open import Data.Rational.Unnormalised using (mkℚᵘ)
open import Relation.Nullary.Decidable using (does)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Slides.Scalar.Model.Rat using (ratMon; ι)
open import Slides.Plot.Ticks ratMon using (ap) public

private
  pow10 : ℕ → ℕ
  pow10 zero    = 1
  pow10 (suc k) = 10 ℕ.* pow10 k

  -- n / d for whole numbers, d ≥ 1 (the constructor takes d − 1)
  ratio : ℕ → ℕ → ℚ
  ratio n d = fromℚᵘ (mkℚᵘ (+ n) (d ∸ 1))

  -- steps as (numerator, denominator), increasing: m / 10ᵏ for k = 4 … 1, then m · 10ᵏ for k = 0 … 6
  steps : List (ℕ × ℕ)
  steps = concatMap (λ k → map (λ m → m , pow10 k) (1 ∷ 2 ∷ 5 ∷ [])) (4 ∷ 3 ∷ 2 ∷ 1 ∷ [])
       ++ concatMap (λ k → map (λ m → m ℕ.* pow10 k , 1) (1 ∷ 2 ∷ 5 ∷ [])) (upTo 7)

  value : ℕ × ℕ → ℚ
  value (n , d) = ratio n d

  last : ℕ × ℕ → List (ℕ × ℕ) → ℕ × ℕ
  last x []       = x
  last _ (y ∷ ys) = last y ys

  -- the first step with `target · step ≥ span`
  pick : ℚ → ℕ → List (ℕ × ℕ) → ℕ × ℕ
  pick span target []       = 1 , 1
  pick span target (s ∷ []) = s
  pick span target (s ∷ ss) = if span ≤ᵇ ι target ℚ.* value s then s else pick span target ss

-- the step as a pair
stepFor : ℕ → ℚ → ℕ × ℕ
stepFor target span = pick span target steps

niceStep : ℕ → ℚ → ℚ
niceStep target span = value (stepFor target span)

-- ticks of `lo … hi`: about `target` of them
ticks : ℕ → ℚ → ℚ → List ℚ
ticks target lo hi = ap (ratio′ kLo ℚ.* step) step count
  where
    st    = stepFor target (hi - lo)
    step  = value st
    inv   = ratio (proj₂ st) (proj₁ st)
    kLo   = ceiling (lo ℚ.* inv)
    kHi   = floor (hi ℚ.* inv)
    ratio′ : ℤ → ℚ
    ratio′ k = fromℚᵘ (mkℚᵘ k 0)
    count : ℕ
    count = if does (kHi ℤ.<? kLo) then 0 else suc ℤ.∣ kHi ℤ.- kLo ∣

-- closed checks
private
  open import Data.Integer using (-[1+_])
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Slides.Plot.Format using (trimmed)
  open import Data.String using (String)

  labels : List ℚ → List String
  labels = map (trimmed 3)

  _ : labels (ticks 5 (+ 0 ℚ./ 1) (+ 10 ℚ./ 1)) ≡ "0" ∷ "2" ∷ "4" ∷ "6" ∷ "8" ∷ "10" ∷ []
  _ = refl
  _ : labels (ticks 5 (-[1+ 0 ] ℚ./ 1) (+ 1 ℚ./ 1)) ≡ "−1" ∷ "−0.5" ∷ "0" ∷ "0.5" ∷ "1" ∷ []
  _ = refl
  _ : labels (ticks 4 (+ 1 ℚ./ 10) (+ 3 ℚ./ 10)) ≡ "0.1" ∷ "0.15" ∷ "0.2" ∷ "0.25" ∷ "0.3" ∷ []
  _ = refl
