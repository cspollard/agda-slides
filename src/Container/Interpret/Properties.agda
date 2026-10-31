{-# OPTIONS --safe --without-K #-}

-- Laws of interpretation: a backend is an algebra, and interpreting is `fold`.
--
--   InitialAlgebra, lambek   `Free₀ C ⊥ˢ` is the initial algebra, so `Free₀ C ⊥ˢ ≅ ⟦ C ⟧ (Free₀ C ⊥ˢ)`
--
-- Algebra homomorphisms commute with folds (`fold-fusion`, in `Container.FreeMonad.Algebraic`), and
-- translating costs nothing (`lower-fusion`, `Container.Lowering.Properties`; `pfold-translate`).

module Container.Interpret.Properties where

open import Level using (Level; Lift; lift; lower)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Container.Core using (Container)
open import Function.Bundles using (Func)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Construction.F-Algebras using (module Lambek)
open import Categories.Functor.Algebra using (F-Algebra)
open import Categories.Object.Initial using (Initial)

open import Container.Polynomial
open import Container.FreeMonad
open import Container.FreeMonad.Algebraic

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
