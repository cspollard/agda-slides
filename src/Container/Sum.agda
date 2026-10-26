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

open import Level using (_⊔_; Level)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Sum.Relation.Binary.Pointwise using (_⊎ₛ_; inj₁; inj₂)
open import Data.Container.Core using (Container)
import Data.Container.Core as CC
open import Data.Container.Combinator using (_⊎_)
open import Data.Container.Relation.Binary.Pointwise
  using (Pointwise) renaming (_,_ to _,ₚ_)
open import Function.Bundles using (Func; Inverse; _⟨$⟩_)
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
  -- The isomorphism

  to-⊎ˢ : Func (Poly₀ (C₁ ⊎ C₂) A) (Poly₀ C₁ A ⊎ₛ Poly₀ C₂ A)
  to-⊎ˢ = record
    { to   = λ { (inj₁ s , f) → inj₁ (s , f) ; (inj₂ s , f) → inj₂ (s , f) }
    ; cong = λ { {inj₁ _ , _} {inj₁ _ , _} (refl ,ₚ f≈g) → inj₁ (refl ,ₚ f≈g)
               ; {inj₂ _ , _} {inj₂ _ , _} (refl ,ₚ f≈g) → inj₂ (refl ,ₚ f≈g) }
    }

  from-⊎ˢ : Func (Poly₀ C₁ A ⊎ₛ Poly₀ C₂ A) (Poly₀ (C₁ ⊎ C₂) A)
  from-⊎ˢ = record
    { to   = λ { (inj₁ (s , f)) → inj₁ s , f ; (inj₂ (s , f)) → inj₂ s , f }
    ; cong = λ { (inj₁ (refl ,ₚ f≈g)) → refl ,ₚ f≈g
               ; (inj₂ (refl ,ₚ f≈g)) → refl ,ₚ f≈g }
    }

  private
    module P₁₂ = Setoid (Poly₀ (C₁ ⊎ C₂) A)
    module S₁₂ = Setoid (Poly₀ C₁ A ⊎ₛ Poly₀ C₂ A)

    from∘to : ∀ x → Func.to from-⊎ˢ (Func.to to-⊎ˢ x) P₁₂.≈ x
    from∘to (inj₁ _ , _) = refl ,ₚ λ _ → A.refl
    from∘to (inj₂ _ , _) = refl ,ₚ λ _ → A.refl

    to∘from : ∀ y → Func.to to-⊎ˢ (Func.to from-⊎ˢ y) S₁₂.≈ y
    to∘from (inj₁ _) = S₁₂.refl
    to∘from (inj₂ _) = S₁₂.refl

  Poly-⊎ : Inverse (Poly₀ (C₁ ⊎ C₂) A) (Poly₀ C₁ A ⊎ₛ Poly₀ C₂ A)
  Poly-⊎ = record
    { to        = Func.to to-⊎ˢ
    ; from      = Func.to from-⊎ˢ
    ; to-cong   = Func.cong to-⊎ˢ
    ; from-cong = Func.cong from-⊎ˢ
    ; inverse   =
        (λ {x} {y} e → S₁₂.trans (Func.cong to-⊎ˢ e) (to∘from x))
      , (λ {x} {y} e → P₁₂.trans (Func.cong from-⊎ˢ e) (from∘to x))
    }

  ----------------------------------------------------------------------
  -- Algebras for a sum

  -- Copairing of two algebras on the same carrier.
  copair : Func (Poly₀ C₁ A) A → Func (Poly₀ C₂ A) A → Func (Poly₀ (C₁ ⊎ C₂) A) A
  copair α₁ α₂ = record
    { to   = λ { (inj₁ s , f) → α₁ ⟨$⟩ (s , f) ; (inj₂ s , f) → α₂ ⟨$⟩ (s , f) }
    ; cong = λ { {inj₁ _ , _} {inj₁ _ , _} (refl ,ₚ f≈g) → Func.cong α₁ (refl ,ₚ f≈g)
               ; {inj₂ _ , _} {inj₂ _ , _} (refl ,ₚ f≈g) → Func.cong α₂ (refl ,ₚ f≈g) }
    }

  copair-inj₁ : ∀ (α₁ : Func (Poly₀ C₁ A) A) (α₂ : Func (Poly₀ C₂ A) A) s f →
                copair α₁ α₂ ⟨$⟩ (inj₁ s , f) A.≈ α₁ ⟨$⟩ (s , f)
  copair-inj₁ α₁ α₂ s f = A.refl

  copair-inj₂ : ∀ (α₁ : Func (Poly₀ C₁ A) A) (α₂ : Func (Poly₀ C₂ A) A) s f →
                copair α₁ α₂ ⟨$⟩ (inj₂ s , f) A.≈ α₂ ⟨$⟩ (s , f)
  copair-inj₂ α₁ α₂ s f = A.refl

  -- Uniqueness: an algebra for the sum is determined by its restrictions.
  copair-unique : ∀ (α₁ : Func (Poly₀ C₁ A) A) (α₂ : Func (Poly₀ C₂ A) A)
                  (β : Func (Poly₀ (C₁ ⊎ C₂) A) A) →
                  (∀ s f → β ⟨$⟩ (inj₁ s , f) A.≈ α₁ ⟨$⟩ (s , f)) →
                  (∀ s f → β ⟨$⟩ (inj₂ s , f) A.≈ α₂ ⟨$⟩ (s , f)) →
                  ∀ {x} → β ⟨$⟩ x A.≈ copair α₁ α₂ ⟨$⟩ x
  copair-unique α₁ α₂ β h₁ h₂ {inj₁ s , f} = h₁ s f
  copair-unique α₁ α₂ β h₁ h₂ {inj₂ s , f} = h₂ s f
