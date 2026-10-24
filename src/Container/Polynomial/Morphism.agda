{-# OPTIONS --safe --without-K #-}

-- Container morphisms are natural transformations between polynomial
-- functors, and the assignment is functorial: identities and composites of
-- container morphisms go to identities and vertical composites.

module Container.Polynomial.Morphism where

open import Level using (Level)
open import Data.Product.Base using (_,_)
open import Data.Container.Core using (Container; _⇒_; shape; position; ⟪_⟫)
import Data.Container.Morphism as CM
open import Data.Container.Relation.Binary.Pointwise
  using () renaming (_,_ to _,ₚ_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl; cong)

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.NaturalTransformation.Equivalence using (_≃_)
import Categories.NaturalTransformation.Core as NT

open import Container.Polynomial

private
  variable
    s p c ℓ : Level

-- The component of the natural transformation at a setoid `X`.

Poly-η : {C D : Container s p} (m : C ⇒ D) (X : Setoid c ℓ) → Func (Poly₀ C X) (Poly₀ D X)
Poly-η m X = record
  { to   = ⟪ m ⟫
  ; cong = λ { {_ , _} {_ , _} (refl ,ₚ f≈g) →
               refl ,ₚ λ p → f≈g (position m p) }
  }

Poly-⇒ : {C D : Container s p} (m : C ⇒ D) →
         NaturalTransformation (Poly {c = c} {ℓ = ℓ} C) (Poly D)
Poly-⇒ m = record
  { η           = Poly-η m
  ; commute     = λ {_} {Y} _ {(_ , _)} → refl ,ₚ λ _ → Setoid.refl Y
  ; sym-commute = λ {_} {Y} _ {(_ , _)} → refl ,ₚ λ _ → Setoid.refl Y
  }

-- Functoriality of `Poly-⇒`.

Poly-id : {C : Container s p} → Poly-⇒ (CM.id C) ≃ NT.id {F = Poly {c = c} {ℓ = ℓ} C}
Poly-id {C = C} {X} = Setoid.refl (Poly₀ C X)

Poly-∘ : {C D E : Container s p} (m : D ⇒ E) (n : C ⇒ D) →
         Poly-⇒ {c = c} {ℓ = ℓ} (m CM.∘ n) ≃ Poly-⇒ m NT.∘ᵥ Poly-⇒ n
Poly-∘ {E = E} _ _ {X} = Setoid.refl (Poly₀ E X)
