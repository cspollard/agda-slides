{-# OPTIONS --safe --without-K #-}

-- Containers are polynomial functors on Setoids.
--
-- A container `S ▷ P` gives the functor `⟦ C ⟧ X = Σ[ s ∈ S ] (P s → X)`; two elements are
-- equal when their shapes are propositionally equal and their continuations pointwise equal
-- in `X` (`Data.Container.Relation.Binary.Equality.Setoid`).  `Poly₁` (post-compose the
-- continuation) makes `Poly C` a functor.  Shapes stay `Set`s compared with `≡`: no signature here
-- needs a quotient on shapes.

module Container.Polynomial where

open import Level using (Level; _⊔_)
open import Data.Product.Base using (_,_)
open import Data.Container.Core using (Container; ⟦_⟧)
import Data.Container.Core as CC
open import Data.Container.Relation.Binary.Pointwise
  using () renaming (_,_ to _,ₚ_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl)
import Data.Container.Relation.Binary.Equality.Setoid as EqS

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)

private
  variable
    s p c ℓ : Level

-- Equality of extensions is the standard-library setoid; `Poly₀ C X` is the setoid of `⟦ C ⟧ X`.

Poly₀ : (C : Container s p) (X : Setoid c ℓ) → Setoid (s ⊔ p ⊔ c) (s ⊔ p ⊔ ℓ)
Poly₀ C X = EqS.setoid X C

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
