{-# OPTIONS --safe --without-K #-}

-- Laws of sums of containers.
--
--   Poly-⊎ : ⟦ C₁ ⊎ C₂ ⟧ A ≅ ⟦ C₁ ⟧ A ⊎ ⟦ C₂ ⟧ A         (an `Inverse` of setoids)
--   copair-inj₁, copair-inj₂ : copair α₁ α₂ restricts to α₁, α₂
--   copair-unique : an algebra for the sum is determined by its two restrictions
--   copairL-inl, copairL-inr : `embed inl ⋙ copairL l m ≈ˡ l`, `embed inr ⋙ copairL l m ≈ˡ m`
--   lower-copairL-inl : `lower (copairL ret h) (translate inl t) ≈⋆ t`, the extension C ↪ C ⊕ E is a
--                       split mono with any lowering `h` of the new commands as retraction
--
-- So algebras for `C₁ ⊎ C₂` on `A` are exactly pairs of algebras (`Container.Sum.copair`).

module Container.Sum.Properties where

open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Sum.Relation.Binary.Pointwise using (_⊎ₛ_; inj₁; inj₂)
open import Data.Container.Core using (Container)
open import Data.Container.Combinator using (_⊎_)
open import Data.Container.Relation.Binary.Pointwise
  using (Pointwise) renaming (_,_ to _,ₚ_)
open import Data.Container.FreeMonad using (_⋆_)
open import Function.Bundles using (Func; Inverse; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl)

open import Container.Polynomial
open import Container.Lowering using (Lowering; embed; _⋙_; lower; translate; ret; _≈⋆_)
open import Container.Lowering.Properties
  using (_≈ˡ_; bind-pure≈; trans≈; sym≈; lower-cong; lower-⋙; lower-embed; lower-ret; refl≈)

import Container.Sum as S

module _ {s₁ s₂ p c ℓ} (C₁ : Container s₁ p) (C₂ : Container s₂ p)
         (A : Setoid c ℓ) where
  private
    module A = Setoid A

  private
    copair = S.copair C₁ C₂ A

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

  -- Algebras for a sum

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

-- Copairing of lowerings restricts to its components.
module _ {s p} {C₁ C₂ E : Container s p} (l : Lowering C₁ E) (m : Lowering C₂ E) where
  copairL-inl : (embed S.inl ⋙ S.copairL l m) ≈ˡ l
  copairL-inl a = bind-pure≈ (l a)

  copairL-inr : (embed S.inr ⋙ S.copairL l m) ≈ˡ m
  copairL-inr a = bind-pure≈ (m a)

-- The extension C ↪ C ⊕ E: translating along `inl` and then lowering the new commands by any `h`
-- (and the old ones by `ret`) is the identity.
module _ {s p c} {C E : Container s p} {X : Set c} (h : Lowering E C) where
  lower-copairL-inl : (t : C ⋆ X) → lower (S.copairL ret h) (translate S.inl t) ≈⋆ t
  lower-copairL-inl t =
    trans≈ (lower-cong (λ a → refl≈ _) (sym≈ (lower-embed S.inl t)))
      (trans≈ (sym≈ (lower-⋙ (embed S.inl) (S.copairL ret h) t))
        (trans≈ (lower-cong (copairL-inl ret h) (refl≈ t)) (lower-ret t)))
