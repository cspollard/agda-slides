{-# OPTIONS --safe --without-K #-}

-- Axes over ℚ: the model of `Slides.Plot.Axis`.  `axisOf lo hi n` shows `lo … hi` on `n` pixels.
-- The ratio is `n / (hi − lo)`; the model fact `ratio · (hi − lo) = n` is not proved but checked
-- when the axis is built (decidable equality in ℚ), and a range that is not an interval (`hi ≤ lo`)
-- falls back to the axis of one value on no pixels, so the constructor is total.

module Slides.Plot.Axis.Rat where

open import Data.Nat using (ℕ)
open import Data.Rational as ℚ using (ℚ; _+_; _-_; _*_; _÷_; 0ℚ; ≢-nonZero)
import Data.Rational.Properties as ℚP
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≢_; refl; sym; trans; cong)

open import Slides.Scalar.Model.Rat using (ratTime; ratSub; ratScale; ι)
import Slides.Plot.Axis ratTime ratSub ratScale as A
open A using (Axis; px; flipY) public

private
  -- a single value on no pixels
  point : ℚ → Axis
  point lo = record
    { lo = lo ; hi = lo ; extent = 0 ; ratio = 0ℚ ; lo≤hi = ℚP.≤-refl ; ratio≥0 = ℚP.≤-refl
    ; span-ratio = trans (cong (0ℚ *_) (ℚP.+-inverseʳ lo)) (ℚP.*-zeroˡ 0ℚ) }

  -- pixels per unit
  perUnit : ℕ → (d : ℚ) → d ≢ 0ℚ → ℚ
  perUnit n d ne = _÷_ (ι n) d {{≢-nonZero ne}}

  build : (lo hi : ℚ) (n : ℕ) → lo ℚ.≤ hi → hi - lo ≢ 0ℚ → Axis
  build lo hi n lh ne with 0ℚ ℚP.≤? perUnit n (hi - lo) ne | (perUnit n (hi - lo) ne * (hi - lo)) ℚP.≟ ι n
  ... | yes nn | yes eq = record
    { lo = lo ; hi = hi ; extent = n ; ratio = perUnit n (hi - lo) ne
    ; lo≤hi = lh ; ratio≥0 = nn ; span-ratio = eq }
  ... | _ | _ = point lo

axisOf : ℚ → ℚ → ℕ → Axis
axisOf lo hi n with lo ℚP.≤? hi | (hi - lo) ℚP.≟ 0ℚ
... | yes lh | no ne = build lo hi n lh ne
... | _ | _ = point lo

-- closed checks: 0 … 10 on 100 pixels; a value outside the range sits at the end
private
  open import Data.Integer using (+_; -[1+_])
  open import Relation.Binary.PropositionalEquality using (_≡_)
  a₀ : Axis
  a₀ = axisOf (+ 0 ℚ./ 1) (+ 10 ℚ./ 1) 100

  _ : px a₀ (+ 5 ℚ./ 1) ≡ 50
  _ = refl
  _ : px a₀ (+ 1 ℚ./ 3) ≡ 3
  _ = refl
  _ : px a₀ (+ 12 ℚ./ 1) ≡ 100
  _ = refl
  _ : px a₀ (-[1+ 2 ] ℚ./ 1) ≡ 0
  _ = refl
  _ : px (axisOf (+ 3 ℚ./ 1) (+ 3 ℚ./ 1) 100) (+ 5 ℚ./ 1) ≡ 0
  _ = refl
