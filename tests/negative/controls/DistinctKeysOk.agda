{-# OPTIONS --safe --without-K #-}

-- Control for ../TwoCommandsOneKey.agda: MUST typecheck (Shift+Space is a different key).

module DistinctKeysOk where

open import Data.List.Base using (_∷_; [])
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (tt)

open import Slides.Input.Nav
open import Slides.Input.Binding using (Decoder)
open import Slides.Backend.Input

ok : Decoder Key Nav
ok = bindKeys ( on _≟Key_ ((space , bare) ∷ []) next
              ∷ on _≟Key_ ((space , shift) ∷ (pageUp , bare) ∷ []) prev
              ∷ [] )
