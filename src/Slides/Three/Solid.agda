{-# OPTIONS --safe --without-K #-}

-- Solids: surfaces made of planar polygons, and how they are painted.
--
-- A `Face` is a planar convex polygon, its vertices in order; a `Solid` is faces under one
-- `Material` (a translucent fill of an opacity in percent, so that the far side shows through the
-- near one, and an opaque rim).  A closed solid hides the faces that turn their backs to the viewer
-- (`closed`); to be told apart, its faces run clockwise on the page when they face the viewer.
--
-- The annular sector is the one shape a detector, a tube or a ring is made of: between two radii,
-- over an angle (in turns) and between two positions along the axis.  Round edges are polygons
-- of `k` segments, the points on the circle given by the polynomials of order `n`.

module Slides.Three.Solid where

open import Data.Bool using (Bool; if_then_else_)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; map; reverse; applyUpTo; _++_)
open import Data.Nat using (ℕ; suc; _∸_)
open import Data.Rational.Unnormalised using (ℚᵘ; mkℚᵘ; 0ℚᵘ; _+_; _*_; _≤ᵇ_)
open import Data.String using (String)

open import Slides.Three.Point

Face : Set
Face = List Point

record Material : Set where
  constructor mat
  field
    fill rim : String
    opacity  : ℕ

record Solid : Set where
  constructor solid
  field
    material : Material
    closed   : Bool
    faces    : List Face

-- the points of the arc at radius r from angle a for w, at z, in k segments
arc : ℕ → ℕ → ℚᵘ → ℚᵘ → ℚᵘ → ℚᵘ → List Point
arc n k r a w z = map (λ j → cyl n r (a + w * mkℚᵘ (+ j) (k ∸ 1)) z) (applyUpTo (λ j → j) (suc k))

-- the wall at angle a between the radii and the positions
wall : ℕ → ℚᵘ → ℚᵘ → ℚᵘ → ℚᵘ → ℚᵘ → Face
wall n r₀ r₁ a z₀ z₁ = cyl n r₀ a z₀ ∷ cyl n r₁ a z₀ ∷ cyl n r₁ a z₁ ∷ cyl n r₀ a z₁ ∷ []

-- the faces of the sector at its two ends and at its two radii (the inner one only if there is one);
-- the open sides are left to `wall`
sector : ℕ → ℕ → ℚᵘ → ℚᵘ → ℚᵘ → ℚᵘ → ℚᵘ → ℚᵘ → List Face
sector n k r₀ r₁ a w z₀ z₁ =
    (arc n k r₁ a w z₁ ++ reverse (arc n k r₀ a w z₁))
  ∷ (arc n k r₁ a w z₀ ++ reverse (arc n k r₀ a w z₀))
  ∷ side r₁ ++ (if r₀ ≤ᵇ 0ℚᵘ then [] else side r₀)
  where side : ℚᵘ → List Face
        side r = (arc n k r a w z₀ ++ reverse (arc n k r a w z₁)) ∷ []

-- the closed sector: its faces and its two walls
annularSector : ℕ → ℕ → ℚᵘ → ℚᵘ → ℚᵘ → ℚᵘ → ℚᵘ → ℚᵘ → List Face
annularSector n k r₀ r₁ a w z₀ z₁ =
  sector n k r₀ r₁ a w z₀ z₁ ++ wall n r₀ r₁ a z₀ z₁ ∷ wall n r₀ r₁ (a + w) z₀ z₁ ∷ []
