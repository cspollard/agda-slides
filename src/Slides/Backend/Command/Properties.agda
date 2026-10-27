{-# OPTIONS --safe --without-K #-}

-- Round trip: a command the backend supports, rendered as a physical input and read back,
-- is the command we started from (`Supports.dec`/`inj` are the two halves).

module Slides.Backend.Command.Properties (V : Set) where

open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Slides.Input.Nav using (Nav)
open import Slides.Input.Binding using (Decoder)
open import Slides.Input.Supports V
open Supports
open import Slides.Backend.Command V

module _ {C I : Set} (b : Supports C) (r : Decoder I (S b)) (render : S b → Maybe I)
         (read-render : ∀ s i → render s ≡ just i → r i ≡ just s) where

  command-render : ∀ {k s i} → inj b k ≡ just s → render s ≡ just i → command b r i ≡ just k
  command-render {k} {s} {i} e ri rewrite read-render s i ri = dec-inj b e
