{-# OPTIONS --safe --without-K #-}

-- A point of space, x to the right, y down the page, z towards the viewer; and the cylindrical
-- coordinates that detectors, tubes and rings are described in: a radius, an angle in turns (from
-- the right, growing clockwise on the page) and a position along the axis.

module Slides.Three.Point where

open import Data.Nat using (ℕ)
open import Data.Rational.Unnormalised using (ℚᵘ; _*_)

open import Slides.Trig using (sin; cos)

record Point : Set where
  constructor point
  field
    x y z : ℚᵘ

-- the point at radius r and angle a (a polynomial of order n) at z
cyl : ℕ → ℚᵘ → ℚᵘ → ℚᵘ → Point
cyl n r a z = point (r * cos n a) (r * sin n a) z
