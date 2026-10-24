{-# OPTIONS --safe --without-K #-}

-- The category of containers and container morphisms, and its two
-- functors out:
--
-- * `PolyFunctor`: a container to its polynomial endofunctor on `Setoids`
--   and a morphism to the natural transformation (`Container.Polynomial.Morphism`);
-- * `EmbedFunctor`: into the category of containers and lowerings
--   (`Container.Lowering.Category`), a morphism being the lowering of each
--   command to one command.
--
-- Arrows are equal when they induce equal natural transformations, which
-- is the pointwise equality of shapes and positions and needs no function
-- extensionality.

module Container.Category where

open import Level using (0ℓ; suc; lift)
open import Data.Product.Base using (_,_)
open import Data.Container.Core using (Container; Position; _⇒_; shape; position; ⟦_⟧; ⟪_⟫)
open import Data.Container.Relation.Binary.Pointwise using (Pointwise) renaming (_,_ to _,ₚ_)
import Data.Container.Morphism as CM
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl)
open import Relation.Binary.PropositionalEquality using (setoid)

open import Categories.Category.Core using (Category)
open import Categories.Category.Construction.Functors using (Functors)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)

open import Container.Polynomial
open import Container.Polynomial.Morphism
open import Container.Lowering
open import Container.Lowering.Category using (Lowerings)

-- Equality of container morphisms: they act equally on every extension.
infix 4 _≈ᶜ_
_≈ᶜ_ : ∀ {C D : Container 0ℓ 0ℓ} → C ⇒ D → C ⇒ D → Set (suc 0ℓ)
_≈ᶜ_ {C} {D} m n = ∀ (X : Setoid 0ℓ 0ℓ) (x : ⟦ C ⟧ (Setoid.Carrier X)) →
                   Pointwise D (Setoid._≈_ X) (⟪ m ⟫ x) (⟪ n ⟫ x)

reflᶜ : ∀ {C D : Container 0ℓ 0ℓ} {m : C ⇒ D} → m ≈ᶜ m
reflᶜ {D = D} X x = Setoid.refl (Poly₀ D X)

symᶜ : ∀ {C D : Container 0ℓ 0ℓ} {m n : C ⇒ D} → m ≈ᶜ n → n ≈ᶜ m
symᶜ {D = D} e X x = Setoid.sym (Poly₀ D X) (e X x)

transᶜ : ∀ {C D : Container 0ℓ 0ℓ} {m n o : C ⇒ D} → m ≈ᶜ n → n ≈ᶜ o → m ≈ᶜ o
transᶜ {D = D} e e′ X x = Setoid.trans (Poly₀ D X) (e X x) (e′ X x)

Containers : Category (suc 0ℓ) 0ℓ (suc 0ℓ)
Containers = record
  { Obj       = Container 0ℓ 0ℓ
  ; _⇒_       = _⇒_
  ; _≈_       = _≈ᶜ_
  ; id        = CM.id _
  ; _∘_       = CM._∘_
  ; assoc     = λ {_} {_} {_} {D} X x → Setoid.refl (Poly₀ D X)
  ; sym-assoc = λ {_} {_} {_} {D} X x → Setoid.refl (Poly₀ D X)
  ; identityˡ = λ {_} {B} X x → Setoid.refl (Poly₀ B X)
  ; identityʳ = λ {_} {B} X x → Setoid.refl (Poly₀ B X)
  ; identity² = λ {A} X x → Setoid.refl (Poly₀ A X)
  ; equiv     = record { refl = reflᶜ ; sym = symᶜ ; trans = transᶜ }
  ; ∘-resp-≈  = λ {_} {_} {_} {f} {h} {g} {i} f≈h g≈i X x → Setoid.trans (Poly₀ _ X) (Func.cong (Poly-η f X) (g≈i X x)) (f≈h X (⟪ i ⟫ x))
  }

PolyFunctor : Functor Containers (Functors (Setoids 0ℓ 0ℓ) (Setoids 0ℓ 0ℓ))
PolyFunctor = record
  { F₀           = Poly
  ; F₁           = Poly-⇒
  ; identity     = λ {C} {X} → Setoid.refl (Poly₀ C X)
  ; homomorphism = λ {_} {_} {Z} {_} {_} {X} → Setoid.refl (Poly₀ Z X)
  ; F-resp-≈     = λ e {X} {x} → e X x
  }

EmbedFunctor : Functor Containers Lowerings
EmbedFunctor = record
  { F₀           = λ C → C
  ; F₁           = embed
  ; identity     = λ a → refl , λ q → lift refl
  ; homomorphism = λ a → refl , λ q → lift refl
  ; F-resp-≈     = embed-resp
  }
  where
    embed-resp : ∀ {C D : Container 0ℓ 0ℓ} {f g : C ⇒ D} → f ≈ᶜ g → embed f ≈ˡ embed g
    embed-resp {C} e a =
      let w = e (setoid (Position C a)) (a , λ q → q)
      in Pointwise.shape w , λ q → lift (Pointwise.position w q)
