{-# OPTIONS --safe --without-K #-}

-- The first instance of `Clock` (`docs/Time.md` section 7): ℚ with `ratO`, the strict comparison
-- `_<ᵇℚ_` and the tick clock `ι n = n/1` of `Slides.Diagram.NatQ`.  Its laws are
-- `Slides.Time.Properties.ratLaws`.

module Slides.Time.Rat where

open import Data.Rational using (ℚ)

open import Slides.Diagram.Ordered using (ratO; _<ᵇℚ_)
open import Slides.Time

ratClock : Clock
ratClock = record { T = ℚ ; O = ratO ; _<ᵇ_ = _<ᵇℚ_ }
