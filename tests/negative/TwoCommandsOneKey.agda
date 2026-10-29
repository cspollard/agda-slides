{-# OPTIONS --safe --without-K #-}

-- Must NOT typecheck: `next` and `prev` both bound to Space.  A table of kinds is sound when no
-- key is in two of them (`clash-free`, decided by computation), and the statement is false.
-- EXPECT: false != true
-- Control: controls/DistinctKeysOk.agda.

module TwoCommandsOneKey where

open import Data.Bool.Base using (true)
open import Data.List.Base using (_∷_; [])
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Slides.Program.Navigation using (Nav; next; prev)
open import Slides.Backend.Input

bad : clash-free ((⟨ space ⟩ ∷ [] , next) ∷ (⟨ space ⟩ ∷ ⟨ pageUp ⟩ ∷ [] , prev) ∷ []) ≡ true
bad = refl
