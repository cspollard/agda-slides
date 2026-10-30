{-# OPTIONS --safe --without-K #-}

-- The tick model: ℕ.  Subtraction is the monus, a percentage is the floor of a product, and
-- scaling is multiplication (ℕ is an ordered module over itself).  No coupling: no ratios.

module Slides.Scalar.Model.Nat where

open import Data.Nat as ℕ using (ℕ; _+_; _*_; _∸_; _/_)
import Data.Nat.Properties as ℕP
import Data.Nat.DivMod as ℕD
open import Relation.Binary.PropositionalEquality using (refl)

open import Slides.Scalar.Core
open import Slides.Scalar.Space
open import Slides.Scalar.Time
open import Data.Product.Base using (_,_)

natMon : OrdMon ℕ
natMon = record
  { 0# = 0 ; _+_ = _+_ ; _⊔_ = ℕ._⊔_ ; _≤_ = ℕ._≤_ ; _≤?_ = ℕ._≤?_
  ; +-assoc = ℕP.+-assoc ; +-comm = ℕP.+-comm ; +-idˡ = λ _ → refl ; +-cancelˡ = ℕP.+-cancelˡ-≡
  ; ≤-refl = ℕP.≤-refl ; ≤-trans = ℕP.≤-trans ; ≤-antisym = ℕP.≤-antisym ; ≤-total = ℕP.≤-total
  ; +-mono = ℕP.+-mono-≤ ; ⊔-ub₁ = ℕP.m≤m⊔n ; ⊔-ub₂ = ℕP.m≤n⊔m ; ⊔-lub = ℕP.⊔-lub }

natSub : Sub natMon
natSub = record { _-_ = _∸_ ; sub-add = ℕP.m+[n∸m]≡n }

natSpace : Space ℕ
natSpace = record
  { ord = natMon ; sub = natSub ; pct = λ p x → (x * p) / 100
  ; pct-100 = λ x → ℕD.m*n/n≡m x 100
  ; pct-mono = λ p x≤y → ℕD./-monoˡ-≤ 100 (ℕP.*-monoˡ-≤ p x≤y) }

natScale : Scale natMon ℕ
natScale = record
  { 0r = 0 ; 1r = 1 ; _+r_ = _+_ ; _*r_ = _*_ ; _≤r_ = ℕ._≤_ ; _·_ = _*_
  ; ·-1 = ℕP.*-identityˡ ; ·-zero = λ _ → refl ; ·-* = ℕP.*-assoc
  ; ·-+ = λ r s x → ℕP.*-distribʳ-+ x r s ; ·-dist = ℕP.*-distribˡ-+ ; ·-mono = λ {r} _ → ℕP.*-monoʳ-≤ r }

natTime : Time ℕ
natTime = record
  { ord = natMon ; tick = λ n → n ; floor = λ n → n
  ; tick-0 = refl ; tick-+ = λ _ _ → refl ; tick-mono = λ h → h ; tick-reflect = λ h → h
  ; floor-gal = λ _ → (λ h → h) , (λ h → h) }
