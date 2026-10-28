{-# OPTIONS --safe --without-K #-}

-- The continuous model: ℚ (the standard library's, no instance search).  Subtraction is
-- exact everywhere, a percentage is multiplication by `p/100`, and scaling is ℚ over itself.

module Slides.Scalar.Model.Rat where

open import Data.Integer using (+_)
open import Data.Nat using (ℕ)
open import Data.Rational as ℚ using (ℚ; _/_; _+_; _*_; _-_; _⊔_; _≤_; 0ℚ; 1ℚ)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Slides.Scalar.Core
open import Slides.Scalar.Space

ratMon : OrdMon ℚ
ratMon = record
  { 0# = 0ℚ ; _+_ = _+_ ; _⊔_ = _⊔_ ; _≤_ = _≤_ ; _≤?_ = ℚP._≤?_
  ; +-assoc = ℚP.+-assoc ; +-comm = ℚP.+-comm ; +-idˡ = ℚP.+-identityˡ
  ; +-cancelˡ = λ a b c e → trans (sym (ℚP.+-identityˡ b))
      (trans (cong (λ y → y + b) (sym (ℚP.+-inverseˡ a)))
        (trans (ℚP.+-assoc (ℚ.- a) a b)
          (trans (cong (λ y → (ℚ.- a) + y) e)
            (trans (sym (ℚP.+-assoc (ℚ.- a) a c))
              (trans (cong (λ y → y + c) (ℚP.+-inverseˡ a)) (ℚP.+-identityˡ c))))))
  ; ≤-refl = ℚP.≤-refl ; ≤-trans = ℚP.≤-trans ; ≤-antisym = ℚP.≤-antisym ; ≤-total = ℚP.≤-total
  ; +-mono = ℚP.+-mono-≤ ; ⊔-ub₁ = λ a b → ℚP.p≤p⊔q a b ; ⊔-ub₂ = λ a b → ℚP.p≤q⊔p a b ; ⊔-lub = ℚP.⊔-lub }

ratSub : Sub ratMon
ratSub = record
  { _-_ = _-_
  ; sub-add = λ {a} {b} _ → trans (ℚP.+-comm b (a - b))
      (trans (ℚP.+-assoc a (ℚ.- b) b) (trans (cong (λ y → a + y) (ℚP.+-inverseˡ b)) (ℚP.+-identityʳ a))) }

-- a percentage is multiplication by `p/100`
ratPct : ℕ → ℚ → ℚ
ratPct p x = (+ p / 100) * x

ratSpace : Space ℚ
ratSpace = record
  { ord = ratMon ; sub = ratSub ; pct = ratPct
  ; pct-100 = ℚP.*-identityˡ
  ; pct-mono = λ p x≤y → ℚP.*-monoˡ-≤-nonNeg (+ p / 100) {{ℚP.normalize-nonNeg p 100}} x≤y }

ratScale : Scale ratMon ℚ
ratScale = record
  { 0r = 0ℚ ; 1r = 1ℚ ; _+r_ = _+_ ; _*r_ = _*_ ; _≤r_ = _≤_ ; _·_ = _*_
  ; ·-1 = ℚP.*-identityˡ ; ·-zero = ℚP.*-zeroˡ ; ·-* = ℚP.*-assoc
  ; ·-+ = λ r s x → ℚP.*-distribʳ-+ x r s ; ·-dist = ℚP.*-distribˡ-+
  ; ·-mono = λ {r} 0≤r x≤y → ℚP.*-monoˡ-≤-nonNeg r {{ℚ.nonNegative 0≤r}} x≤y }
