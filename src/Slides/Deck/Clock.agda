{-# OPTIONS --safe --without-K #-}

-- The deck clock: the scene algebra on whole ticks with no drivers, and `Flow` leaves overlaid by
-- `++`.  `E` (events) and `S` (pointwise reading) are instantiated here once for every module that
-- reads a deck.

module Slides.Deck.Clock where

open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ)

open import Slides.Scalar.Model.Nat using (natMon; natSub)
open import Slides.Diagram.Overlay using (listOverlay)
open import Slides.Deck.Content using (Flow)
import Slides.Scene.Events as Events
import Slides.Scene.Sample as Sample

module E = Events {ℕ} {⊥} natMon natSub
module S = Sample {ℕ} {⊥} {Flow} natMon natSub (λ ()) listOverlay
