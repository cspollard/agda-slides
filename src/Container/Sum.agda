{-# OPTIONS --safe --without-K #-}

-- The polynomial functor of a sum of containers is the sum of the
-- polynomial functors:
--
--   ⟦ C₁ ⊎ C₂ ⟧ A ≅ ⟦ C₁ ⟧ A ⊎ ⟦ C₂ ⟧ A       (natural in the setoid A)
--
-- and, consequently, algebras for `C₁ ⊎ C₂` on a carrier `A` are exactly
-- pairs of algebras for `C₁` and `C₂` on `A` (`copair`, with its universal
-- property).  This is how backends for separate slide vocabularies are
-- combined.

module Container.Sum where

open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Sum.Relation.Binary.Pointwise using (inj₁; inj₂)
open import Data.Container.Core using (Container)
import Data.Container.Core as CC
open import Data.Container.Combinator using (_⊎_)
open import Data.Container.Relation.Binary.Pointwise
  using (Pointwise) renaming (_,_ to _,ₚ_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl)

open import Container.Polynomial

-- The injections of the sum, as container morphisms.
module _ {s₁ s₂ p} {C₁ : Container s₁ p} {C₂ : Container s₂ p} where
  inl : C₁ CC.⇒ (C₁ ⊎ C₂)
  inl = record { shape = inj₁ ; position = λ x → x }

  inr : C₂ CC.⇒ (C₁ ⊎ C₂)
  inr = record { shape = inj₂ ; position = λ x → x }

module _ {s₁ s₂ p c ℓ} (C₁ : Container s₁ p) (C₂ : Container s₂ p)
         (A : Setoid c ℓ) where
  private
    module A = Setoid A

  ----------------------------------------------------------------------
  -- Algebras for a sum

  -- Copairing of two algebras on the same carrier.
  copair : Func (Poly₀ C₁ A) A → Func (Poly₀ C₂ A) A → Func (Poly₀ (C₁ ⊎ C₂) A) A
  copair α₁ α₂ = record
    { to   = λ { (inj₁ s , f) → α₁ ⟨$⟩ (s , f) ; (inj₂ s , f) → α₂ ⟨$⟩ (s , f) }
    ; cong = λ { {inj₁ _ , _} {inj₁ _ , _} (refl ,ₚ f≈g) → Func.cong α₁ (refl ,ₚ f≈g)
               ; {inj₂ _ , _} {inj₂ _ , _} (refl ,ₚ f≈g) → Func.cong α₂ (refl ,ₚ f≈g) }
    }
