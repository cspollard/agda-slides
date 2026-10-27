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

open import Data.List using (List; map)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)

open import Slides.Diagram using (Style)

-- A named region: `left` and `top` (half units) of its corner relative to the
-- frame's top-left corner, `width` and `height` (units).
--
--   (0,0)+---------------+
--        |  (left,top)   |
--        |       +----+  |   the origin is the top-left of the frame;
--        |       |    | height   x grows right, y grows DOWN
--        |       +----+  |
--        +---------------+
--                width
record Box (S : Set) : Set where
  constructor box
  field
    left top width height : S

data Draw (S : Set) : Set where
  rect   : (x y w h : S) → Style → Draw S
  circle : (cx cy r : S) → Style → Draw S
  line   : (x₁ y₁ x₂ y₂ : S) → Style → Draw S
  arrow  : (x₁ y₁ x₂ y₂ : S) → Style → Draw S
  -- a circle is given by its centre (not its corner); a line goes from its
  -- first point to its second; an arrow also, with the head at the second
  -- text centred at a point: the font size is a plain number
  label  : (x y : S) (size : ℕ) → String → Style → Draw S

-- A sized frame with what is drawn in it (all drawn relative to the frame's
-- top-left corner, in the order of the list, so later is on top) and the boxes
-- that have been given a name.  The size is the frame a neighbour sees; the
-- drawings may stick out of it (`Place`), and are not counted in it.
record Layout (S : Set) : Set where
  constructor layout
  field
    width   : S
    height  : S
    -- drawn with the top-left corner at the origin
    draws   : List (Draw S)
    anchors : List (String × Box S)

------------------------------------------------------------------------
-- Change of scalar (the action on maps; see `Slides.Diagram.Layout.Properties`)

mapBox : ∀ {S T} → (S → T) → Box S → Box T
mapBox f (box l t w h) = box (f l) (f t) (f w) (f h)

mapDraw : ∀ {S T} → (S → T) → Draw S → Draw T
mapDraw f (rect x y w h s)     = rect (f x) (f y) (f w) (f h) s
mapDraw f (circle x y r s)     = circle (f x) (f y) (f r) s
mapDraw f (line a b c d s)     = line (f a) (f b) (f c) (f d) s
mapDraw f (arrow a b c d s)    = arrow (f a) (f b) (f c) (f d) s
mapDraw f (label x y n t s)    = label (f x) (f y) n t s

mapAnchor : ∀ {S T} → (S → T) → String × Box S → String × Box T
mapAnchor f (n , b) = n , mapBox f b

mapLayout : ∀ {S T} → (S → T) → Layout S → Layout T
mapLayout f l = layout (f (Layout.width l)) (f (Layout.height l))
                       (map (mapDraw f) (Layout.draws l)) (map (mapAnchor f) (Layout.anchors l))
