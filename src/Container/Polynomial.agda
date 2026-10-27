{-# OPTIONS --safe --without-K #-}

-- Containers are polynomial functors on Setoids.
--
-- A container `C = S ▷ P` determines the functor
--
--   ⟦ C ⟧ X = Σ[ s ∈ S ] (P s → X)
--
-- from `Setoids c ℓ` to `Setoids (s ⊔ p ⊔ c) (s ⊔ p ⊔ ℓ)`, where two elements
-- are equal when their shapes are propositionally equal and their
-- continuations are pointwise equal in `X` (stdlib's
-- `Data.Container.Relation.Binary.Pointwise`).  When the container lives
-- in `Set 0ℓ` this is an endofunctor on `Setoids c ℓ`.

module Container.Polynomial where

open import Level using (Level; _⊔_; 0ℓ)
open import Data.Product.Base using (_,_)
open import Data.Container.Core using (Container; ⟦_⟧)
import Data.Container.Core as CC
open import Data.Container.Relation.Binary.Pointwise
  using (Pointwise) renaming (_,_ to _,ₚ_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality.Core
  using (refl; sym; trans)

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor; Endofunctor)

private
  variable
    s p c ℓ : Level

module _ (C : Container s p) (X : Setoid c ℓ) where
  private module X = Setoid X

  -- Equality of extensions is an equivalence relation.

  poly-isEquivalence : IsEquivalence (Pointwise C X._≈_)
  poly-isEquivalence = record
    { refl  = refl ,ₚ λ _ → X.refl
    ; sym   = sym′
    ; trans = trans′
    }
    where
      sym′ : ∀ {x y} → Pointwise C X._≈_ x y → Pointwise C X._≈_ y x
      sym′ {_ , _} {_ , _} (refl ,ₚ f≈g) = refl ,ₚ λ p → X.sym (f≈g p)

      trans′ : ∀ {x y z} → Pointwise C X._≈_ x y → Pointwise C X._≈_ y z →
               Pointwise C X._≈_ x z
      trans′ {_ , _} {_ , _} {_ , _} (refl ,ₚ f≈g) (refl ,ₚ g≈h) =
        refl ,ₚ λ p → X.trans (f≈g p) (g≈h p)

  Poly₀ : Setoid (s ⊔ p ⊔ c) (s ⊔ p ⊔ ℓ)
  Poly₀ = record
    { Carrier       = ⟦ C ⟧ X.Carrier
    ; _≈_           = Pointwise C X._≈_
    ; isEquivalence = poly-isEquivalence
    }

-- Action on morphisms: post-compose the continuation.

module _ (C : Container s p) {X : Setoid c ℓ} {Y : Setoid c ℓ} where
  private
    module X = Setoid X
    module Y = Setoid Y

  Poly₁ : Func X Y → Func (Poly₀ C X) (Poly₀ C Y)
  Poly₁ g = record
    { to   = CC.map (g ⟨$⟩_)
    ; cong = λ { (e ,ₚ f≈f′) → e ,ₚ λ p → Func.cong g (f≈f′ p) }
    }

-- The polynomial functor of a container.

Poly : (C : Container s p) →
       Functor (Setoids c ℓ) (Setoids (s ⊔ p ⊔ c) (s ⊔ p ⊔ ℓ))
Poly C = record
  { F₀           = Poly₀ C
  ; F₁           = Poly₁ C
  ; identity     = λ {A} {(_ , _)} → refl ,ₚ λ _ → Setoid.refl A
  ; homomorphism = λ {_} {_} {Z} {_} {_} {(_ , _)} → refl ,ₚ λ _ → Setoid.refl Z
  ; F-resp-≈     = λ f≈g {(_ , _)} → refl ,ₚ λ _ → f≈g
  }

-- Containers in `Set 0ℓ` give endofunctors.

Poly-Endo : Container 0ℓ 0ℓ → Endofunctor (Setoids c ℓ)
Poly-Endo = Poly
