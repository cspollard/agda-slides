{-# OPTIONS --safe --without-K #-}

-- Closed checks of `Slides.Three.Render.facing`: a square that runs clockwise on the page (y down)
-- faces the viewer, the same square reversed does not, and the flat view keeps it so; a box shows
-- exactly three faces in a view turned and tipped either way, and a cylinder shows one cap.
-- `make test-numeric`.

module ThreeCheck where

open import Data.Bool using (true; false)
open import Data.Integer using (+_)
open import Data.List using (List; _∷_; []; map; filterᵇ; length)
open import Data.Nat using (ℕ)
open import Data.Rational.Unnormalised using (ℚᵘ; mkℚᵘ; 0ℚᵘ; 1ℚᵘ; -_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Slides.Three.Point
open import Slides.Three.View
open import Slides.Three.Solid using (Face; box; cylinder)
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

shown : View → List Face → ℕ
shown V fs = length (filterᵇ facing (map (map (rotate V)) fs))

cube : List Face
cube = box (- 1ℚᵘ) 1ℚᵘ (- 1ℚᵘ) 1ℚᵘ (- 1ℚᵘ) 1ℚᵘ

_ : shown (viewP (mkℚᵘ (+ 1) 4) (mkℚᵘ (+ 1) 5) 0ℚᵘ) cube ≡ 3
_ = refl

_ : shown (viewP (- mkℚᵘ (+ 1) 4) (mkℚᵘ (+ 1) 5) 0ℚᵘ) cube ≡ 3
_ = refl

_ : shown (viewP (mkℚᵘ (+ 1) 4) (- mkℚᵘ (+ 1) 5) (mkℚᵘ (+ 1) 9)) cube ≡ 3
_ = refl

_ : shown (viewP (- mkℚᵘ (+ 1) 4) (- mkℚᵘ (+ 1) 5) 0ℚᵘ) cube ≡ 3
_ = refl

-- a cylinder of 8 segments seen end on, a little tipped: its near cap and the near half of its side
_ : shown (viewP 0ℚᵘ (mkℚᵘ (+ 1) 5) 0ℚᵘ) (cylinder 5 8 1ℚᵘ (- 1ℚᵘ) 1ℚᵘ) ≡ 5
_ = refl
