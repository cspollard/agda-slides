{-# OPTIONS --safe --without-K #-}

-- The first instance of `Clock`: ℚ, with the tick clock `ι n = n/1` of `Slides.Diagram.NatQ`.
-- Every field is a law of the ordered abelian group ℚ (or of `ι`, already proved in
-- `Slides.Diagram.NatQ.Properties`); nothing computes in ℚ.

module Slides.Spike.Stage4.QClock where

open import Data.Bool using (Bool; true; false; not; T)
open import Data.Nat as ℕ using (ℕ)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _≤_; _≤ᵇ_)
import Data.Rational.Properties as ℚP
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)

open import Slides.Diagram.NatQ using (ι)
open import Slides.Diagram.NatQ.Properties using (ι-+; ι-≤ᵇ)
open import Slides.Spike.Stage4.Clock

-- as `Slides.Anim.Continuous._<ᵗ_`
_<ᵗ_ : ℚ → ℚ → Bool
τ <ᵗ σ = not (σ ≤ᵇ τ)

private
  a≤a+b : ∀ a b → 0ℚ ≤ b → a ≤ a ℚ.+ b
  a≤a+b a b h = ℚP.≤-trans (ℚP.≤-reflexive (sym (ℚP.+-identityʳ a))) (ℚP.+-monoʳ-≤ a h)

  nlt′ : ∀ a b → 0ℚ ≤ b → ((a ℚ.+ b) <ᵗ a) ≡ false
  nlt′ a b h with a ≤ᵇ (a ℚ.+ b) in eq
  ... | true  = refl
  ... | false = ⊥-elim (subst-T eq (ℚP.≤⇒≤ᵇ (a≤a+b a b h)))
    where
      subst-T : ∀ {x : Bool} → x ≡ false → T x → _
      subst-T refl ()

  +-minus′ : ∀ a b → ((a ℚ.+ b) ℚ.- a) ≡ b
  +-minus′ a b = trans (cong (ℚ._- a) (ℚP.+-comm a b))
                  (trans (ℚP.+-assoc b a (ℚ.- a))
                    (trans (cong (b ℚ.+_) (ℚP.+-inverseʳ a)) (ℚP.+-identityʳ b)))

  nonneg-ι′ : ∀ n → 0ℚ ≤ ι n
  nonneg-ι′ n = ℚP.≤ᵇ⇒≤ (subst T (sym (ι-≤ᵇ 0 n)) tt)

  nonneg-+′ : ∀ {a b} → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a ℚ.+ b
  nonneg-+′ {a} {b} ha hb = ℚP.≤-trans (a≤a+b 0ℚ b hb) (ℚP.+-monoˡ-≤ b ha)
    -- 0 ≤ 0 + b ≤ a + b

QClock : Clock
QClock = record
  { T = ℚ ; _+_ = ℚ._+_ ; _-_ = ℚ._-_ ; _<ᵇ_ = _<ᵗ_ ; ι = ι ; Nonneg = 0ℚ ≤_
  ; +-assoc = ℚP.+-assoc ; ι-+ = ι-+ ; +-minus = +-minus′ ; nlt = nlt′
  ; nonneg-ι = nonneg-ι′ ; nonneg-+ = nonneg-+′ }

-- the nested-clock law, at ℚ
open Sem QClock public using (nested-flat; nested-at; nested-at-flat)
