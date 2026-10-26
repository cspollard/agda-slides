{-# OPTIONS --safe --without-K #-}

-- Laws of interpretation: `Free₀ C ⊥` is the initial `⟦C⟧`-algebra (Lambek's lemma), folding commutes with algebra
-- homomorphisms, and fusion: interpreting a translated program is interpreting with the pulled-back algebra.
module Container.Interpret.Properties where

open import Level using (Level; Lift; lift; lower)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (⊤; tt)
open import Data.Container.Core using (Container; _⇒_; position; ⟪_⟫)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Data.Container.Relation.Binary.Pointwise
  using () renaming (_,_ to _,ₚ_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl)

open import Categories.Category.Construction.F-Algebras using (module Lambek)
open import Categories.Functor.Algebra
  using (F-Algebra; F-Algebra-Morphism)
open import Categories.Object.Initial using (Initial)

open import Container.Polynomial
open import Container.Polynomial.Morphism using (Poly-η)
open import Container.FreeMonad
open import Container.FreeMonad.Algebraic

import Container.Interpret as I

module Initiality {s p} (c ℓ : Level) (C : Container s p) where
  open Alg c ℓ C

  -- The empty setoid.
  ⊥ˢ : Setoid c′ ℓ′
  ⊥ˢ = record
    { Carrier       = Lift c′ ⊥
    ; _≈_           = λ _ _ → Lift ℓ′ ⊤
    ; isEquivalence = record
        { refl = lift tt ; sym = λ _ → lift tt ; trans = λ _ _ → lift tt }
    }

  empty : ∀ (A : Setoid c′ ℓ′) → Func ⊥ˢ A
  empty A = record
    { to   = λ x → ⊥-elim (lower x)
    ; cong = λ {x} _ → ⊥-elim (lower x)
    }

  -- `Free₀ C ⊥ˢ` is the initial algebra.
  InitialAlgebra : Initial Alg
  InitialAlgebra = record
    { ⊥            = FreeAlg ⊥ˢ
    ; ⊥-is-initial = record
        { !        = λ {A} → fold-morphism A (empty (F-Algebra.A A))
        ; !-unique = λ {A} g →
            Setoid.sym (F-Algebra.A A)
              (fold-unique A (empty (F-Algebra.A A)) g (λ {x} → ⊥-elim (lower x)))
        }
    }

  -- Lambek's lemma: `Free₀ C ⊥ˢ ≅ ⟦ C ⟧ (Free₀ C ⊥ˢ)`.
  open Lambek InitialAlgebra public using (lambek)

module Fusion {s p} (c ℓ : Level) (C : Container s p) where
  open Alg c ℓ C

  -- Folding commutes with algebra homomorphisms.
  fold-hom : ∀ {A B : F-Algebra F} {X : Setoid c′ ℓ′}
             (h : F-Algebra-Morphism A B) (f : Func X (F-Algebra.A A))
             (t : C ⋆ Setoid.Carrier X) →
             Setoid._≈_ (F-Algebra.A B)
               (F-Algebra-Morphism.f h ⟨$⟩ fold A f t)
               (fold B {X} (record { to   = λ x → F-Algebra-Morphism.f h ⟨$⟩ (f ⟨$⟩ x)
                               ; cong = λ e → Func.cong (F-Algebra-Morphism.f h) (Func.cong f e)
                               }) t)
  fold-hom {A} {B} {X} h f (pure _)         = Setoid.refl (F-Algebra.A B)
  fold-hom {A} {B} {X} h f (impure (_ , k)) =
    Setoid.trans (F-Algebra.A B) (F-Algebra-Morphism.commutes h)
      (Func.cong (F-Algebra.α B) (refl ,ₚ λ q → fold-hom {X = X} h f (k q)))

module Translate {s p} (c ℓ : Level) (C D : Container s p) (m : C ⇒ D) where
  module AC = Alg c ℓ C
  module AD = Alg c ℓ D
  open AC using (c′; ℓ′)
  open I.Translate c ℓ C D m using (translate)

  -- Pull an algebra for `D` back to an algebra for `C`.
  pullback : F-Algebra AD.F → F-Algebra AC.F
  pullback B = record
    { A = F-Algebra.A B
    ; α = record
        { to   = λ t → F-Algebra.α B ⟨$⟩ ⟪ m ⟫ t
        ; cong = λ e → Func.cong (F-Algebra.α B) (Func.cong (Poly-η m (F-Algebra.A B)) e)
        }
    }

  -- Fusion: interpreting the translation equals interpreting with the
  -- pulled-back algebra.
  fusion : ∀ (B : F-Algebra AD.F) {X : Setoid c′ ℓ′}
           (f : Func X (F-Algebra.A B)) (t : C ⋆ Setoid.Carrier X) →
           Setoid._≈_ (F-Algebra.A B)
             (AD.fold B f (translate t)) (AC.fold (pullback B) f t)
  fusion B f (pure _)         = Setoid.refl (F-Algebra.A B)
  fusion B f (impure (_ , k)) =
    Func.cong (F-Algebra.α B) (refl ,ₚ λ q → fusion B f (k (position m q)))
