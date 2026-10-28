{-# OPTIONS --safe --without-K #-}

-- The frame-by-frame reading of an animation: the ℕ clock.
--
-- `Slides.Anim.Sample` reads an animation in any clock.  In the tick clock (`Slides.Time.Nat`)
-- a track is read at its whole ticks (`natVal`: the sample of the track, in whole units), the
-- result is a duration `n` and a function of the tick, and a timeline is its values at the ticks
-- `0 .. n-1`.  A tick at which nothing is shown (a gap) is the empty frame.  `Par` is the overlay
-- `atop` (`Slides.Diagram.Place`) frame by frame, with absence the unit; `Seq` and `Delay` shift
-- the tick; there is no list algebra to prove laws about, the laws are those of `Sem`
-- (`Slides.Time.Properties`) at the clock ℕ.

module Slides.Anim.Timeline where

open import Data.List using (List; applyUpTo)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Nat as ℕ using (ℕ)
open import Data.Rational using (ℚ)
open import Data.Product using (_,_; proj₁; proj₂)

open import Slides.Diagram.Syntax using (Dia; spacer)
open import Slides.Diagram.Ordered using (zero′)
import Slides.Anim.Track as T
open import Slides.Time.Nat using (natClock)
open import Slides.Anim.Syntax
open import Slides.Anim.Sample

-- the parameter of a track at a tick, in whole units
natVal : T.Track ℚ → ℕ → ℕ
natVal tr k = units (proj₂ (T.sample T.ℚLerp tr) k)

-- what each tick shows, and for how long
framesN : Anim → TM natClock (Dia ℕ)
framesN = frames natClock natVal

-- the values of a timed function at the ticks `0 .. n-1`, `x₀` where nothing is shown
tabulate : ∀ {X : Set} → X → TM natClock X → List X
tabulate x₀ (n , f) = applyUpTo (λ k → fromMaybe x₀ (f k)) n

timeline : Anim → List (Dia ℕ)
timeline a = tabulate (spacer 0 0) (framesN a)
