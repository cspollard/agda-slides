{-# OPTIONS --safe --without-K #-}

-- Must NOT typecheck: presenting a deck on a backend whose `Supports` lacks `Nav`.
-- `present` demands `NavTotal`, and `printS` (a print backend) supports no command, so the
-- evidence `inj printS (inj₁ n) ≡ just _` has no proof: `nothing` is not `just _`.
-- The rejection is a type error, not an instance failure (see the EXPECT line).
-- EXPECT: Maybe.nothing !=
-- Control: controls/NavBackendOk.agda (the same deck on `revealSupports`).

module NoNavBackend where

open import Data.Unit.Base using (⊤)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality.Core using (refl)

open import Slides.Input ⊤
open import Slides.Input.Supports ⊤
open Supports

bad : Prog (S (printS {⊤})) ⊤
bad = present (printS {⊤}) (λ n → _ , refl) pause
