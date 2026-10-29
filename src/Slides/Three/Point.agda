{-# OPTIONS --safe --without-K #-}

-- A point of space in cylindrical coordinates: a radius, an angle in 1/1024 turns (from the right,
-- growing clockwise on the page, y being downwards) and a position along the axis in hundredths
-- (towards the viewer is positive).

module Slides.Three.Point where

open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ)

record Point : Set where
  constructor cyl
  field
    r a : ℕ
    z   : ℤ
