{-# OPTIONS --safe --without-K #-}

-- The free monad on a container, as a monad on Setoids.
--
-- The carrier of `Free₀ C X` is stdlib's `C ⋆ X` (trees of `C`-operations
-- with leaves in `X`).  Two trees are equal when they have the same shape
-- at every node (propositionally) and equal leaves in `X`.  Since the
-- equality is defined structurally, no function extensionality is needed
-- for the monad laws.

module Container.FreeMonad where

open import Level using (Level; _⊔_; Lift; lift)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_,_; Σ-syntax)
open import Data.Container.Core using (Container; Position)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
open import Function.Bundles using (Func)
open import Function.Base using (id)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst)

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)
open import Categories.Monad using (Monad)
open import Categories.NaturalTransformation using ()
import Categories.NaturalTransformation.Core as NT

private
  variable
    s p c ℓ : Level

------------------------------------------------------------------------
-- Equality of trees

module _ {C : Container s p} (X : Setoid c ℓ) where
  private module X = Setoid X

  -- Defined by recursion rather than as an inductive family so that its
  -- universe level does not depend on the level of the carrier of `X`.
  Eq : C ⋆ X.Carrier → C ⋆ X.Carrier → Set (ℓ ⊔ s ⊔ p)
  Eq (pure x)          (pure y)          = Lift (s ⊔ p) (x X.≈ y)
  Eq (pure _)          (impure _)        = Lift (ℓ ⊔ s ⊔ p) ⊥
  Eq (impure _)        (pure _)          = Lift (ℓ ⊔ s ⊔ p) ⊥
  Eq (impure (s₁ , k)) (impure (s₂ , k′)) =
    Σ[ e ∈ s₁ ≡ s₂ ] (∀ q → Eq (k q) (k′ (subst (Position C) e q))) 

  refl⋆ : ∀ t → Eq t t
  refl⋆ (pure x)         = lift X.refl
  refl⋆ (impure (_ , k)) = refl , λ q → refl⋆ (k q)

  sym⋆ : ∀ {t u} → Eq t u → Eq u t
  sym⋆ {pure _}          {pure _}          (lift e) = lift (X.sym e)
  sym⋆ {pure _}          {impure _}        ()
  sym⋆ {impure _}        {pure _}          ()
  sym⋆ {impure (_ , _)}  {impure (_ , _)}  (refl , f) = refl , λ q → sym⋆ (f q)

  trans⋆ : ∀ {t u v} → Eq t u → Eq u v → Eq t v
  trans⋆ {pure _} {pure _} {pure _} (lift e) (lift e′) = lift (X.trans e e′)
  trans⋆ {pure _}   {pure _}   {impure _} _  ()
  trans⋆ {pure _}   {impure _} {_}        () _
  trans⋆ {impure _} {pure _}   {_}        () _
  trans⋆ {impure _} {impure _} {pure _}   _  ()
  trans⋆ {impure (_ , _)} {impure (_ , _)} {impure (_ , _)}
         (refl , f) (refl , g) = refl , λ q → trans⋆ (f q) (g q)

  Eq-isEquivalence : IsEquivalence Eq
  Eq-isEquivalence = record { refl = refl⋆ _ ; sym = sym⋆ ; trans = trans⋆ }

Free₀ : (C : Container s p) → Setoid c ℓ → Setoid (c ⊔ s ⊔ p) (ℓ ⊔ s ⊔ p)
Free₀ C X = record
  { Carrier       = C ⋆ Setoid.Carrier X
  ; _≈_           = Eq X
  ; isEquivalence = Eq-isEquivalence X
  }

------------------------------------------------------------------------
-- The monad structure

-- Operations on carriers.

module _ {C : Container s p} where

  fmap : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → C ⋆ A → C ⋆ B
  fmap f t = t >>= λ x → pure (f x)

  join : ∀ {a} {A : Set a} → C ⋆ (C ⋆ A) → C ⋆ A
  join t = t >>= id
