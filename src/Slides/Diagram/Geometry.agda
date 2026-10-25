{-# OPTIONS --safe --without-K #-}

-- The vocabulary of placement shared by the diagram syntax and its layout
-- interpretation: boxes, the points on them that arrows attach to, and
-- alignments.

module Slides.Diagram.Geometry where

open import Data.Nat using (ℕ; _+_; _*_; _/_; _∸_)
open import Data.Product using (_×_; _,_)

-- A rectangle: left, top, width, height.
record Box : Set where
  constructor box
  field
    left top width height : ℕ

shiftBox : ℕ → ℕ → Box → Box
shiftBox dx dy (box l t w h) = box (l + dx) (t + dy) w h

-- The points of a box that a connection can attach to.
data Side : Set where
  north south east west middle : Side

-- A point along a side, in percent from the left (north, south) or the top
-- (east, west): `at north 40` is two fifths of the way along the top edge.
-- It spreads several connections over one edge.
data Port : Set where
  side : Side → Port
  at   : Side → ℕ → Port

point : Side → Box → ℕ × ℕ
point north  (box l t w h) = l + w / 2 , t
point south  (box l t w h) = l + w / 2 , t + h
point east   (box l t w h) = l + w , t + h / 2
point west   (box l t w h) = l , t + h / 2
point middle (box l t w h) = l + w / 2 , t + h / 2

portPoint : Port → Box → ℕ × ℕ
portPoint (side s)      b             = point s b
portPoint (at north p)  (box l t w h) = l + (w * p) / 100 , t
portPoint (at south p)  (box l t w h) = l + (w * p) / 100 , t + h
portPoint (at east p)   (box l t w h) = l + w , t + (h * p) / 100
portPoint (at west p)   (box l t w h) = l , t + (h * p) / 100
portPoint (at middle p) b             = point middle b

-- Alignment of a row (vertically) and of a column (horizontally).
data VAlign : Set where
  top middle bottom : VAlign

data Align : Set where
  left centred right : Align

-- centre an extent `inner` inside `outer`
centre : ℕ → ℕ → ℕ
centre outer inner = (outer ∸ inner) / 2

-- offset of an extent of size `inner` inside `outer`
valignOffset : VAlign → ℕ → ℕ → ℕ
valignOffset top    outer inner = 0
valignOffset middle outer inner = centre outer inner
valignOffset bottom outer inner = outer ∸ inner

alignOffset : Align → ℕ → ℕ → ℕ
alignOffset left    outer inner = 0
alignOffset centred outer inner = centre outer inner
alignOffset right   outer inner = outer ∸ inner
