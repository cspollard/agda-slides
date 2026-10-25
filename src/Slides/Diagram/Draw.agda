{-# OPTIONS --safe --without-K #-}

-- The data a layout is made of, over a scalar `S`: boxes, drawing commands and
-- the layout record itself.  The operations on them are in
-- `Slides.Diagram.Place`.
--
-- Half units.  Sizes (`width`, `height`, a rectangle's `w h`, a radius) are in
-- diagram units, but *positions* (a box's `left` and `top`, every coordinate of
-- a drawing command) are in half units, so centring a box in a frame is the
-- difference of the sizes, with no division.  `Place.toElement` halves the
-- positions when the layout becomes a `Diagram`.

module Slides.Diagram.Draw where

open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Data.String using (String)

open import Slides.Diagram using (Style; Element)

-- left, top (half units), width, height
record Box (S : Set) : Set where
  constructor box
  field
    left top width height : S

data Draw (S : Set) : Set where
  rect   : (x y w h : S) → Style → Draw S
  circle : (cx cy r : S) → Style → Draw S
  line   : (x₁ y₁ x₂ y₂ : S) → Style → Draw S
  arrow  : (x₁ y₁ x₂ y₂ : S) → Style → Draw S
  -- text centred at a point: the font size is a plain number
  label  : (x y : S) (size : ℕ) → String → Style → Draw S
  -- an element in the final diagram's own coordinates: it does not move
  fixed  : Element → Draw S

record Layout (S : Set) : Set where
  constructor layout
  field
    width   : S
    height  : S
    -- drawn with the top-left corner at the origin
    draws   : List (Draw S)
    anchors : List (String × Box S)
