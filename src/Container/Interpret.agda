{-# OPTIONS --safe --without-K #-}

-- Translation of programs along a container morphism, the operation fusion is stated for.
--
--   translate m : C ⋆ X → D ⋆ X       renames each command by `shape m`, re-indexes continuations by `position m`
--
-- Its laws with folds are in `Container.Interpret.Properties`; with lowerings, in
-- `Container.Lowering.Translate`.

module Container.Interpret where

open import Level using (Level)
open import Data.Product.Base using (_,_)
open import Data.Container.Core using (Container; _⇒_; shape; position)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)


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
