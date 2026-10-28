{-# OPTIONS --safe --without-K #-}

-- Laws of `polyline` (`Slides.Diagram.Place`): a connected line through points.
--
--   * no points, no ink and an empty frame; one point, no ink and a frame that reaches it;
--   * `n` points draw `n - 1` lines;
--   * the frame is the extent of the points from the origin (the definition, restated).
--
-- That a polyline is natural in the scalar, valid, and has the size `sizeAlgebra` says, is in
-- `Slides.Diagram.Layout.Properties`, `Valid` and `Laws`, with the other primitives.

open import Slides.Diagram.Scalar using (Ops)

module Slides.Diagram.Place.Properties.Polyline {S : Set} (O : Ops S) where

open import Data.List using (List; []; _∷_; length; map)
import Data.List.Properties as LP
open import Data.Nat using (ℕ; suc; _∸_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import Slides.Diagram using (Style)
open import Slides.Diagram.Draw using (Layout; layout)
open import Slides.Diagram.Place O

open Ops O using (0#; _⊔_)

polyline-nil : ∀ s → polyline [] s ≡ layout 0# 0# [] []
polyline-nil s = refl

polyline-one : ∀ p s → polyline (p ∷ []) s ≡ layout (proj₁ p ⊔ 0#) (proj₂ p ⊔ 0#) [] []
polyline-one p s = refl

-- the frame of a polyline is the extent of its points
polyline-size : ∀ pts s →
  (Layout.width (polyline pts s) , Layout.height (polyline pts s))
  ≡ (maximum (map proj₁ pts) , maximum (map proj₂ pts))
polyline-size pts s = refl

length-pairs : ∀ {A : Set} (xs : List A) → length (pairs xs) ≡ length xs ∸ 1
length-pairs []             = refl
length-pairs (a ∷ [])       = refl
length-pairs (a ∷ b ∷ rest) = cong suc (length-pairs (b ∷ rest))

-- `n` points draw `n - 1` lines
polyline-lines : ∀ pts s → length (Layout.draws (polyline pts s)) ≡ length pts ∸ 1
polyline-lines pts s = trans (LP.length-map (chord s) (pairs pts)) (length-pairs pts)
