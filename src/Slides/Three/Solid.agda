{-# OPTIONS --safe --without-K #-}

-- Solids: surfaces made of planar polygons, and how they are painted.
--
-- A `Face` is a planar convex polygon, its vertices in order; a `Solid` is faces under one
-- `Material` (a translucent fill of an opacity in percent, so that the far side shows through the
-- near one, and an opaque rim).  A closed solid hides the faces that turn their backs to the viewer
-- (`closed`); to be told apart, its faces run clockwise on the page when they face the viewer.
--
-- `box` and `cylinder` are closed solids' faces, clockwise on the page seen from outside.
--
-- The annular sector is the one shape a detector, a tube or a ring is made of: between two radii,
-- over an angle (in turns) and between two positions along the axis.  Round edges are polygons
-- of `k` segments, the points on the circle given by the polynomials of order `n`.

module Slides.Three.Solid where

open import Data.Bool using (Bool; if_then_else_)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; map; reverse; applyUpTo; _++_)
open import Data.Nat using (ℕ; suc; _∸_)
open import Data.Rational.Unnormalised using (ℚᵘ; mkℚᵘ; 0ℚᵘ; 1ℚᵘ; _+_; _*_; _≤ᵇ_)
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

-- the faces of the box between x₀ x₁, y₀ y₁ and z₀ z₁ (z₁ nearer the viewer; y down)
box : ℚᵘ → ℚᵘ → ℚᵘ → ℚᵘ → ℚᵘ → ℚᵘ → List Face
box x₀ x₁ y₀ y₁ z₀ z₁ =
    quad (λ a b → point a b z₁) x₀ x₁ y₀ y₁            -- front
  ∷ quad (λ a b → point a b z₀) x₁ x₀ y₀ y₁            -- back
  ∷ quad (λ a b → point x₁ b a) z₁ z₀ y₀ y₁            -- right
  ∷ quad (λ a b → point x₀ b a) z₀ z₁ y₀ y₁            -- left
  ∷ quad (λ a b → point a y₀ b) x₀ x₁ z₀ z₁            -- top
  ∷ quad (λ a b → point a y₁ b) x₁ x₀ z₀ z₁            -- bottom
  ∷ []
  where quad : (ℚᵘ → ℚᵘ → Point) → ℚᵘ → ℚᵘ → ℚᵘ → ℚᵘ → Face
        quad f a₀ a₁ b₀ b₁ = f a₀ b₀ ∷ f a₁ b₀ ∷ f a₁ b₁ ∷ f a₀ b₁ ∷ []

-- the closed cylinder of radius r along the axis from z₀ to z₁, round in k segments: the sector
-- of a whole turn about the axis (no inner radius, no walls), its side cut into one face per segment
cylinder : ℕ → ℕ → ℚᵘ → ℚᵘ → ℚᵘ → List Face
cylinder n k r z₀ z₁ =
    arc n k r 0ℚᵘ 1ℚᵘ z₁ ∷ reverse (arc n k r 0ℚᵘ 1ℚᵘ z₀)
  ∷ map (λ j → let a = mkℚᵘ (+ j) (k ∸ 1); w = mkℚᵘ (+ 1) (k ∸ 1) in
               arc n 1 r a w z₀ ++ reverse (arc n 1 r a w z₁)) (applyUpTo (λ j → j) k)
