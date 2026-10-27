{-# OPTIONS --safe --without-K #-}

-- Laws of the content lowerings: `finalFrame` of a loop, and of an animation with no steps, is the first frame.
module Slides.Lower.Properties where

open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Container.Lowering
open import Slides.Core

open import Slides.Lower

finalFrame-looping : ∀ d ds → finalFrame d ds looping ≡ d
finalFrame-looping d ds = refl

finalFrame-no-steps : ∀ d ds → finalFrame d ds (onSteps []) ≡ d
finalFrame-no-steps d []        = refl
finalFrame-no-steps d (f ∷ fs)  = refl
