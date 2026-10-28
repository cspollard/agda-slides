{-# OPTIONS --safe --without-K #-}

-- Coupling: how durations drive lengths.  A moving value is a term of this signature.
--
-- Over a Time with its exact-subtraction layer and an ordered module of ratios on the same
-- carrier (lengths and durations share the ordered monoid), `Coupling` adds: the `ratio` of two
-- durations; the easing `ease` of a ratio (`Easing`: the curves fixing 0 and 1; Bézier is
-- deferred); and, derived, interpolation `lerp r a b = a + r·(b - a)` and the `progress` of an
-- instant in an interval.  A tick is read as a length by `tick` (Time).  Everything here is a
-- consequence of the laws below and of the other theories; ℕ has no model (no ratios of
-- durations), so Coupling is the layer ℚ adds.
--
-- Signature: `CouplingC` (ratio, ease, lerp); its handler needs the ratios to be the scalar.

module Slides.Scalar.Coupling where

open import Level using (0ℓ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ)
open import Data.Container.Core using (Container; _▷_)
open import Data.Unit using (⊤)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
import Relation.Binary.PropositionalEquality.Properties as ≡P

open import Container.Interpret.Plain using (Handler; Congruent)
open import Slides.Scalar.Core
open import Slides.Scalar.Space using (Scale)
open import Slides.Scalar.Time

data Easing : Set where
  Linear Step StepStart : Easing

record Coupling {K R} (Tm : Time K) (Sb : Sub (Time.ord Tm)) (Sc : Scale (Time.ord Tm) R) : Set₁ where
  open Time Tm
  open Sub Sb
  open Scale Sc
  field
    ratio        : K → K → R
    ease         : Easing → R → R
    ratio-scale  : ∀ r d → ¬ (d ≡ 0#) → ratio (r · d) d ≡ r
    ease-0       : ∀ e → ease e 0r ≡ 0r
    ease-1       : ∀ e → ease e 1r ≡ 1r
    ease-linear  : ∀ r → ease Linear r ≡ r

  -- interpolation between two lengths by a ratio
  lerp : R → K → K → K
  lerp r a b = a + r · (b - a)

  lerp-0 : ∀ a b → lerp 0r a b ≡ a
  lerp-0 a b = trans (cong (a +_) (·-zero (b - a))) (+-idʳ a)

  lerp-1 : ∀ {a b} → a ≤ b → lerp 1r a b ≡ b
  lerp-1 {a} {b} a≤b = trans (cong (a +_) (·-1 (b - a))) (sub-add a≤b)

  -- a duration against itself is the ratio 1
  ratio-self : ∀ d → ¬ (d ≡ 0#) → ratio d d ≡ 1r
  ratio-self d d≢0 = trans (cong (λ y → ratio y d) (sym (·-1 d))) (ratio-scale 1r d d≢0)

  ratio-zero : ∀ d → ¬ (d ≡ 0#) → ratio 0# d ≡ 0r
  ratio-zero d d≢0 = trans (cong (λ y → ratio y d) (sym (·-zero d))) (ratio-scale 0r d d≢0)

  -- eased progress of the instant `t` in an interval of duration `d`
  progress : Easing → K → K → R
  progress e t d = ease e (ratio t d)

  progress-start : ∀ e d → ¬ (d ≡ 0#) → progress e 0# d ≡ 0r
  progress-start e d d≢0 = trans (cong (ease e) (ratio-zero d d≢0)) (ease-0 e)

  progress-end : ∀ e d → ¬ (d ≡ 0#) → progress e d d ≡ 1r
  progress-end e d d≢0 = trans (cong (ease e) (ratio-self d d≢0)) (ease-1 e)

  -- a moving value runs from `a` to `b`: it starts at `a`, and ends at `b` (as `a ≤ b`)
  move-start : ∀ e a b d → ¬ (d ≡ 0#) → lerp (progress e 0# d) a b ≡ a
  move-start e a b d d≢0 = trans (cong (λ r → lerp r a b) (progress-start e d d≢0)) (lerp-0 a b)

  move-end : ∀ e {a b} d → a ≤ b → ¬ (d ≡ 0#) → lerp (progress e d d) a b ≡ b
  move-end e d a≤b d≢0 = trans (cong (λ r → lerp r _ _) (progress-end e d d≢0)) (lerp-1 a≤b)

------------------------------------------------------------------------
-- The signature

data CouplingOp : Set where
  Ratio Lerp : CouplingOp
  Ease : Easing → CouplingOp

couplingArity : CouplingOp → Set
couplingArity Ratio    = Fin 2
couplingArity Lerp     = Fin 3
couplingArity (Ease _) = ⊤

CouplingC : Container 0ℓ 0ℓ
CouplingC = CouplingOp ▷ couplingArity

module _ {K} {Tm : Time K} {Sb : Sub (Time.ord Tm)} {Sc : Scale (Time.ord Tm) K} (C : Coupling Tm Sb Sc) where
  open Coupling C

  couplingH : Handler CouplingC K
  couplingH Ratio    k = ratio (k zero) (k (suc zero))
  couplingH Lerp     k = lerp (k zero) (k (suc zero)) (k (suc (suc zero)))
  couplingH (Ease e) k = ease e (k _)

  couplingCong : Congruent CouplingC (≡P.setoid K) couplingH
  couplingCong Ratio    e = cong₂ ratio (e zero) (e (suc zero))
  couplingCong Lerp {k} {k′} e rewrite e zero | e (suc zero) | e (suc (suc zero)) = refl
  couplingCong (Ease x) e = cong (ease x) (e _)
