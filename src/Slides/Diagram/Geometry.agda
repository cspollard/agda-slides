{-# OPTIONS --safe --without-K #-}

-- The vocabulary of placement shared by the diagram syntax and its layout
-- interpretation: the points on a box that arrows attach to, and alignments.
-- (Boxes and the arithmetic on them are in `Slides.Diagram.Draw` and
-- `Slides.Diagram.Place`, which are parametrised by a scalar.)

module Slides.Diagram.Geometry where

open import Data.Nat using (ℕ)

-- The points of a box that a connection can attach to.
data Side : Set where
  north south east west middle : Side

-- A point along a side, in percent from the left (north, south) or the top
-- (east, west): `at north 40` is two fifths of the way along the top edge.
-- It spreads several connections over one edge.
data Port : Set where
  side : Side → Port
  at   : Side → ℕ → Port

-- Alignment of a row (vertically) and of a column (horizontally).
data VAlign : Set where
  top middle bottom : VAlign

data Align : Set where
  left centred right : Align
