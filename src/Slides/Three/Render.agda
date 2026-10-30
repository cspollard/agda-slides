{-# OPTIONS --safe --without-K #-}

-- Drawing solids as a diagram, by the painter's algorithm: project every vertex by the view, drop
-- the faces of a closed solid that turn their backs (`facing`: vertices clockwise on the page),
-- sort the rest by mean vertex depth, farthest first (ties in the order given), and draw each
-- as a translucent fill under an opaque rim, in a frame `w` by `h` about the view's centre.
--
-- Right for convex faces that do not interpenetrate (shells, boxes, cells), wrong for others; then
-- the caller orders the solids.  The result is a list of layers, nearest first (`layers` in
-- `Slides.Diagram.Convenience`).

module Slides.Three.Render where

open import Data.Bool using (Bool; true; _∨_; not; if_then_else_)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; map; reverse; foldr; concatMap; filterᵇ; length)
open import Data.Nat using (ℕ; _∸_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (ℚᵘ; mkℚᵘ; 0ℚᵘ; _+_; _-_; _*_; _≤ᵇ_)

open import Slides.Diagram.Convenience
open import Slides.Diagram.Style using (filled; stroked; thick; faded)
open import Slides.Three.Point
open import Slides.Three.View
open import Slides.Three.Solid

-- does a face turn towards the viewer: its first three vertices run clockwise on the page (y down)
facing : Face → Bool
facing (p ∷ q ∷ r ∷ _) = 0ℚᵘ ≤ᵇ ((x q - x p) * (y r - y p) - (y q - y p) * (x r - x p))
  where x = Point.x; y = Point.y
facing _ = true

-- the mean depth of the vertices
depthOf : Face → ℚᵘ
depthOf f = foldr (λ p s → Point.z p + s) 0ℚᵘ f * mkℚᵘ (+ 1) (length f ∸ 1)

-- insertion sort by depth, the farthest first
insert : ∀ {A : Set} → ℚᵘ × A → List (ℚᵘ × A) → List (ℚᵘ × A)
insert p []       = p ∷ []
insert p (q ∷ qs) = if proj₁ p ≤ᵇ proj₁ q then p ∷ q ∷ qs else q ∷ insert p qs

render : ℕ → ℕ → ℕ → ℕ → View → List Solid → List (Dia ℕ)
render w h cx cy V ss = concatMap (λ { (_ , s , g) → paint (Solid.material s) g }) (reverse (foldr insert [] keyed))
  where
    placed : List (Solid × Face)
    placed = concatMap (λ s → map (λ f → s , map (rotate V) f) (Solid.faces s)) ss
    shown = filterᵇ (λ { (s , g) → not (Solid.closed s) ∨ facing g }) placed
    keyed = map (λ { (s , g) → depthOf g , s , g }) shown
    layer : Dia ℕ → Dia ℕ
    layer = place w h 0 0
    paint : Material → Face → List (Dia ℕ)
    paint (mat fl rm o) g =
        layer (polygon ps (faded o (thick 0 (stroked fl (filled fl defaultStyle)))))
      ∷ layer (polygon ps (thick 1 (stroked rm defaultStyle))) ∷ []
      where ps = map (screen cx cy) g
