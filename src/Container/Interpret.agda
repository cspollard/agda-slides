{-# OPTIONS --safe --without-K #-}

-- Interpretation of programs in the free monad, i.e. folds into algebras.
--
-- A *backend* for a container `C` is an `⟦C⟧`-algebra.  Interpreting a
-- program is `fold`, the unique algebra homomorphism out of the free
-- algebra (see `Container.FreeMonad.Algebraic`).  This module collects the
-- consequences we use for backends:
--
-- * `Free₀ C ⊥` is the initial `⟦C⟧`-algebra, hence satisfies Lambek's lemma;
-- * folding commutes with algebra homomorphisms (backends can be post-processed);
-- * fusion: translating a program along a container morphism and then
--   interpreting it is the same as interpreting with the pulled-back algebra.

module Container.Interpret where

open import Level using (Level)
open import Data.Product.Base using (_,_)
open import Data.Container.Core using (Container; _⇒_; shape; position)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Data.Container.Relation.Binary.Pointwise
  using () renaming (_,_ to _,ₚ_)
open import Function.Bundles using (Func)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl)

open import Categories.Functor.Algebra
  using (F-Algebra; F-Algebra-Morphism)
open import Categories.Object.Initial using (Initial)

open import Container.Polynomial
open import Container.FreeMonad
open import Container.FreeMonad.Algebraic

module Translate {s p} (c ℓ : Level) (C D : Container s p) (m : C ⇒ D) where
  module AC = Alg c ℓ C
  module AD = Alg c ℓ D
  open AC using (c′; ℓ′)

  -- Translate a program along a container morphism.
  translate : ∀ {X : Set c′} → C ⋆ X → D ⋆ X
  translate (pure x)          = pure x
  translate (impure (s₁ , k)) =
    impure (shape m s₁ , λ q → translate (k (position m q)))
