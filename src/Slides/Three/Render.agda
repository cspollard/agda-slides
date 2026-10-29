{-# OPTIONS --safe --without-K #-}

-- Drawing solids as a diagram: the painter's algorithm.
--
--   1. every vertex is turned once by the view;
--   2. a face of a closed solid that turns its back to the viewer is dropped (`facing`: its
--      vertices run clockwise on the page);
--   3. the faces are ordered by the mean depth of their vertices, the farthest first, equal depths
--      in the order given;
--   4. each is a translucent fill with an opaque rim over it, in a frame `w` by `h`, about the
--      centre (cx , cy) of the view.
--
-- This is right for convex faces that do not interpenetrate (shells, boxes, cells) and wrong for
-- others; when it matters, the caller orders the solids.  The result is a list of layers, the
-- nearest first (see `layers` in `Slides.Diagram.Convenience`).

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
