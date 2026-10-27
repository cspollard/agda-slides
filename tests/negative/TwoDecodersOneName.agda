{-# OPTIONS --safe --without-K #-}

-- Must NOT typecheck: two decoders that accept the same input.  The standalone backend reads
-- the key name only, so ArrowRight cannot be both `next` and `last`; the decoders are not
-- `Disjoint`.
-- Control: controls/DistinctNamesOk.agda.

module TwoDecodersOneName where

open import Data.List.Base using (_∷_; [])
open import Data.Unit.Base using (tt)

open import Slides.Input.Nav
open import Slides.Input.Binding using (Decoder)
open import Slides.Backend.Input

bad : Decoder KeyName Nav
bad = bindNames ( on _≟K_ (arrowRight ∷ space ∷ []) next
                ∷ on _≟K_ (end ∷ arrowRight ∷ []) last
                ∷ [] )
