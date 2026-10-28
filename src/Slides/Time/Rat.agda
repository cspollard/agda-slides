{-# OPTIONS --safe --without-K #-}

-- THEORY MODULE (proofs; no executable imports it).  The first instance of `Clock` (`docs/Time.md`
-- section 7): ℚ with `ratO`, the strict comparison `_<ᵇℚ_` and the tick clock `ι n = n/1` of
-- `Slides.Diagram.NatQ`.  Every field is a law already proved (`NatQ.Properties`,
-- `Ordered.Properties`); nothing computes in ℚ.

module Slides.Time.Rat where

open import Data.Rational using (ℚ)
open import Relation.Binary.PropositionalEquality using (refl)

open import Slides.Diagram.Ordered using (ratO; _<ᵇℚ_)
open import Slides.Diagram.Ordered.Properties using (ratQLaws; ι-<ᵇ)
open import Slides.Diagram.NatQ.Properties using (ι-+; ι-∸)
open import Slides.Time

ratClock : Clock
ratClock = record
  { T = ℚ ; O = ratO ; _<ᵇ_ = _<ᵇℚ_
  ; laws = ratQLaws ; lt-spec = λ _ _ _ _ → refl
  ; ι-0 = refl ; ι-+ = ι-+ ; ι-<ᵇ = ι-<ᵇ ; ι-∸ = ι-∸ }
