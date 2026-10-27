{-# OPTIONS --safe --without-K #-}

-- Control for ../NoNavBackend.agda: MUST typecheck.  The same stand-ins with a backend
-- that does support `Nav`, so the negative test fails because of the missing `Nav` and
-- not because of a typo in the stand-ins.  TODO: switch to Slides.Input.Supports together
-- with NoNavBackend.agda.

module NavBackendOk where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Nav : Set where
  next prev first last : Nav
  goto : ℕ → Nav

record Supports : Set₁ where
  field
    S   : Set
    inj : Nav → Maybe S
open Supports

NavTotal : Supports → Set
NavTotal b = ∀ n → Σ[ s ∈ S b ] inj b n ≡ just s

present : (b : Supports) → NavTotal b → ⊤
present _ _ = tt

navOnly : Supports
navOnly = record { S = Nav ; inj = just }

ok : ⊤
ok = present navOnly (λ n → n , refl)
