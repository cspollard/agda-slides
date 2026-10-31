{-# OPTIONS --safe --without-K #-}

-- Sums of containers: the injections `inl`, `inr`, and copairing of algebras.
--
--   copair : (⟦ C₁ ⟧ A → A) → (⟦ C₂ ⟧ A → A) → (⟦ C₁ ⊎ C₂ ⟧ A → A)
--
--   copairL : Lowering C₁ E → Lowering C₂ E → Lowering (C₁ ⊎ C₂) E
--
-- This is how backends for separate vocabularies combine.  The universal property
-- and `⟦ C₁ ⊎ C₂ ⟧ ≅ ⟦ C₁ ⟧ ⊎ ⟦ C₂ ⟧` are in `Container.Sum.Properties`.

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
open import Container.Lowering using (Lowering)

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

  -- Algebras for a sum

  -- Copairing of two algebras on the same carrier.
  copair : Func (Poly₀ C₁ A) A → Func (Poly₀ C₂ A) A → Func (Poly₀ (C₁ ⊎ C₂) A) A
  copair α₁ α₂ = record
    { to   = λ { (inj₁ s , f) → α₁ ⟨$⟩ (s , f) ; (inj₂ s , f) → α₂ ⟨$⟩ (s , f) }
    ; cong = λ { {inj₁ _ , _} {inj₁ _ , _} (refl ,ₚ f≈g) → Func.cong α₁ (refl ,ₚ f≈g)
               ; {inj₂ _ , _} {inj₂ _ , _} (refl ,ₚ f≈g) → Func.cong α₂ (refl ,ₚ f≈g) }
    }

-- Copairing of lowerings: the coproduct in the category of lowerings.
module _ {s p} {C₁ C₂ E : Container s p} where
  copairL : Lowering C₁ E → Lowering C₂ E → Lowering (C₁ ⊎ C₂) E
  copairL l m (inj₁ a) = l a
  copairL l m (inj₂ a) = m a
