{-# OPTIONS --safe --without-K #-}

-- Must NOT typecheck: `next` and `prev` both bound to Space.  `bindKeys` accepts kinds only
-- when they are pairwise `Disjoint` on all keys, decided by computation, so the instance
-- argument has no instance.
-- Control: controls/DistinctKeysOk.agda.

module TwoCommandsOneKey where

open import Data.List.Base using (_∷_; [])
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (tt)   -- the instance of ⊤ that discharges the check

open import Slides.Input.Nav
open import Slides.Input.Binding using (Decoder)
open import Slides.Backend.Input

bad : Decoder Key Nav
bad = bindKeys ( on _≟Key_ ((space , bare) ∷ []) next
               ∷ on _≟Key_ ((space , bare) ∷ (pageUp , bare) ∷ []) prev
               ∷ [] )
