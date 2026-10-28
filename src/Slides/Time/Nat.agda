{-# OPTIONS --safe --without-K #-}

-- The tick clock as a model: ℕ with `natO`, the subtraction a monus.  Its `ι` is the identity, so
-- every law is `refl` (`Slides.Time.Properties.natLaws`).  Reading a scene in this clock is the
-- frame-by-frame reading (`Slides.Anim.Timeline`); the homomorphism `ι : ℕ → ℚ` between the two
-- models is what `Slides.Anim.Assembly` relates them by.

module Slides.Time.Nat where

open import Data.Nat as ℕ using (ℕ)

open import Slides.Diagram.Ordered using (natO)
open import Slides.Time

natClock : Clock
natClock = record { T = ℕ ; O = natO ; _<ᵇ_ = ℕ._<ᵇ_ }
