{-# OPTIONS --safe --without-K #-}

-- Must NOT typecheck: presenting a deck on a backend whose `Supports` lacks `Nav`.
--
-- TODO(Stage 1 port): `Nav`, `Supports` and `present` below are local stand-ins that follow
-- src/Slides/Spike/Input/Backend.agda (`Backend`, `NavTotal`, `present`, `printB`).  Once
-- Slides.Input.Supports exists (branch stage1-core), delete the stand-ins, import the real
-- ones, keep `bad` as is, and move this file to tests/negative/.  Rejection is a type
-- error (`nothing` is not `just _`), not an instance failure, so `make test-negative` needs
-- its "another reason" filter relaxed for this file (see README.md).

module NoNavBackend where

open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- stand-in for Slides.Input.Nav
data Nav : Set where
  next prev first last : Nav
  goto : ℕ → Nav

-- stand-in for Slides.Input.Supports: the vocabulary `S` of the backend and a partial
-- embedding of the navigation commands into it
record Supports : Set₁ where
  field
    S   : Set
    inj : Nav → Maybe S
open Supports

NavTotal : Supports → Set
NavTotal b = ∀ n → Σ[ s ∈ S b ] inj b n ≡ just s

-- stand-in for `present`: a deck needs a backend that supports `Nav`
present : (b : Supports) → NavTotal b → ⊤
present _ _ = tt

-- a print backend supports nothing
printB : Supports
printB = record { S = ⊥ ; inj = λ _ → nothing }

bad : ⊤
bad = present printB (λ n → _ , refl)
