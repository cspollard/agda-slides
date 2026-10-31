{-# OPTIONS --safe --without-K #-}

-- Arithmetic of windows, from the laws of `Slides.Scalar.Core` alone (an ordered monoid with
-- exact subtraction); no computation in a model.  The facts the scene readings need: order is
-- reflected by adding on the left, `o ≤ t - w` iff `w + o ≤ t`, and `(t - w) - o ≡ t - (w + o)`.

open import Slides.Scalar.Core using (OrdMon; Sub)

module Slides.Scene.Arith {T : Set} (M : OrdMon T) (Sb : Sub M) where

open import Data.Empty using (⊥-elim)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open OrdMon M
open Sub Sb

-- not below is above
≰⇒≥ : ∀ {a b} → ¬ (a ≤ b) → b ≤ a
≰⇒≥ {a} {b} n with ≤-total a b
... | inj₁ a≤b = ⊥-elim (n a≤b)
... | inj₂ b≤a = b≤a

+-mono-r : ∀ {a b} c → a ≤ b → c + a ≤ c + b
+-mono-r c h = +-mono ≤-refl h

-- order is reflected by adding on the left
+-reflect-≤ : ∀ a {b c} → a + b ≤ a + c → b ≤ c
+-reflect-≤ a {b} {c} h with ≤-total b c
... | inj₁ b≤c = b≤c
... | inj₂ c≤b = ≤-reflexive (+-cancelˡ a b c (≤-antisym h (+-mono-r a c≤b)))

-- `+` distributes over `⊔`
+-⊔ : ∀ a b c → a + (b ⊔ c) ≡ (a + b) ⊔ (a + c)
+-⊔ a b c with ≤-total b c
... | inj₁ b≤c = trans (cong (a +_) (⊔-≤ b≤c)) (sym (⊔-≤ (+-mono-r a b≤c)))
... | inj₂ c≤b = trans (cong (a +_) (⊔-≥ c≤b)) (sym (⊔-≥ (+-mono-r a c≤b)))

-- a duration added to a non-negative one grows
≤-+ : ∀ {a o} → 0# ≤ o → a ≤ a + o
≤-+ {a} {o} 0≤o = ≤-trans (≤-reflexive (sym (+-idʳ a))) (+-mono-r a 0≤o)

-- non-negative durations add
nn+ : ∀ {a b} → 0# ≤ a → 0# ≤ b → 0# ≤ a + b
nn+ 0≤a 0≤b = ≤-trans (≤-reflexive (sym (+-idˡ 0#))) (+-mono 0≤a 0≤b)

-- subtracting zero
sub-zero : ∀ {a} → 0# ≤ a → a - 0# ≡ a
sub-zero {a} 0≤a = sym (sub-unique 0≤a (+-idˡ a))

-- `o ≤ t - w` iff `w + o ≤ t`, for `w ≤ t`
shift-≤ : ∀ {w t o} → w ≤ t → o ≤ t - w → w + o ≤ t
shift-≤ {w} {t} w≤t h = ≤-trans (+-mono-r w h) (≤-reflexive (sub-add w≤t))

unshift-≤ : ∀ {w t o} → w ≤ t → w + o ≤ t → o ≤ t - w
unshift-≤ {w} {t} w≤t h = +-reflect-≤ w (≤-trans h (≤-reflexive (sym (sub-add w≤t))))

-- local times agree: `(t - w) - o` is `t - (w + o)`
sub-sub : ∀ {w t o} → w ≤ t → o ≤ t - w → (t - w) - o ≡ t - (w + o)
sub-sub {w} {t} {o} w≤t o≤ = sub-unique (shift-≤ w≤t o≤)
  (trans (+-assoc w o _) (trans (cong (w +_) (sub-add o≤)) (sub-add w≤t)))

