{-# OPTIONS --safe --without-K #-}

-- Control for ../TwoCommandsOneKey.agda: MUST typecheck (Shift+Space is a different key).

module DistinctKeysOk where

open import Data.Bool.Base using (true)
open import Data.List.Base using (_∷_; [])
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Slides.Program.Navigation using (Nav; next; prev)
open import Slides.Backend.Input

ok : clash-free ((⟨ space ⟩ ∷ [] , next) ∷ (⇧ space ∷ ⟨ pageUp ⟩ ∷ [] , prev) ∷ []) ≡ true
ok = refl
