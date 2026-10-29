{-# OPTIONS --safe --without-K #-}

-- Closed checks of `Slides.Three.Render.facing`: a square that runs clockwise on the page (y down)
-- faces the viewer, the same square reversed does not, and the flat view keeps it so.
-- `make test-numeric`.

module ThreeCheck where

open import Data.Bool using (true; false)
open import Data.List using (List; _∷_; []; map)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Slides.Three.Point
open import Slides.Three.View
open import Slides.Three.Render

corner : _ → _ → Point
corner x y = point x y 0ℚᵘ

square : List Point
square = corner 0ℚᵘ 0ℚᵘ ∷ corner 1ℚᵘ 0ℚᵘ ∷ corner 1ℚᵘ 1ℚᵘ ∷ corner 0ℚᵘ 1ℚᵘ ∷ []

reversed : List Point
reversed = corner 0ℚᵘ 0ℚᵘ ∷ corner 0ℚᵘ 1ℚᵘ ∷ corner 1ℚᵘ 1ℚᵘ ∷ corner 1ℚᵘ 0ℚᵘ ∷ []

_ : facing square ≡ true
_ = refl

_ : facing reversed ≡ false
_ = refl

_ : facing (map (rotate flat) square) ≡ true
_ = refl

_ : facing (map (rotate flat) reversed) ≡ false
_ = refl
