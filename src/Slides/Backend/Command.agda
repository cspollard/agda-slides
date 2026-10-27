{-# OPTIONS --safe --without-K #-}

-- From a physical input to a command: read the input as a backend command (a decoder into
-- `S b`, see `Slides.Backend.Input`), then decode it with the `Supports`.  Inputs that
-- decode to no command, or to a backend command with no `Nav ⊎ C` meaning, give `nothing`.
-- Law: `Slides.Backend.Command.Properties`.

module Slides.Backend.Command (V : Set) where

open import Data.Maybe.Base using (Maybe; nothing; maybe′)
open import Data.Sum.Base using (_⊎_)

open import Slides.Input.Nav using (Nav)
open import Slides.Input.Binding using (Decoder)
open import Slides.Input.Supports V

command : ∀ {C I} (b : Supports C) → Decoder I (Supports.S b) → Decoder I (Nav ⊎ C)
command b r i = maybe′ (Supports.dec b) nothing (r i)
