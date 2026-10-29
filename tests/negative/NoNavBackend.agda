{-# OPTIONS --safe --without-K #-}

-- Must NOT typecheck: presenting a deck on a backend whose `Supports` binds no command of `Nav`.
-- `presents` demands that every command is bound (`Σ s , inj n ≡ just s`), and for a print
-- backend, which binds none, `nothing` is not `just _`.
-- EXPECT: nothing !=
-- Control: controls/NavBackendOk.agda (the same deck on reveal's and plain's `Supports`).

module NoNavBackend where

open import Data.Empty using (⊥)
open import Data.Maybe.Base using (nothing)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Container.Lowering using (_≈⋆_)

open import Slides.Program.Navigation using (Nav)
open import Slides.Program.Supports using (Supports; skipU)
open import Slides.Program.Syntax using (Program)
open import Slides.Backend.Input.Properties using (presents)

-- a backend that binds nothing
printS : Supports Nav
printS = record
  { S = ⊥ ; _≟S_ = λ () ; inj = λ _ → nothing ; dec = λ _ → nothing
  ; dec-inj = λ () ; inj-dec = λ () }

bad : ∀ {T D A} (p : Program T D Nav A) → skipU printS p ≈⋆ p
bad = presents printS (λ n → _ , refl)
