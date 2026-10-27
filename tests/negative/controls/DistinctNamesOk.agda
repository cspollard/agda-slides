{-# OPTIONS --safe --without-K #-}

-- Control for ../TwoDecodersOneName.agda: MUST typecheck.

module DistinctNamesOk where

open import Data.List.Base using (_∷_; [])
open import Data.Unit.Base using (tt)

open import Slides.Input.Nav
open import Slides.Input.Binding using (Decoder)
open import Slides.Backend.Input

ok : Decoder KeyName Nav
ok = bindNames ( on _≟K_ (arrowRight ∷ space ∷ []) next
               ∷ on _≟K_ (end ∷ []) last
               ∷ [] )
