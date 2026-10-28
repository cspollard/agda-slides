{-# OPTIONS --safe --without-K #-}

-- The vocabulary of placement: where an arrow attaches to a box, and how the smaller of two
-- neighbours sits in the extra room.  No scalar appears here (a percentage is a plain number).
--
--          north              VAlign (Beside):  top | middle | bottom
--       +----N----+           Align  (Above):   left | centred | right
--  west W    M    E east      `at north 40`: 40% along the top edge
--       +----S----+
--          south

module Slides.Diagram.Geometry where

open import Data.Nat using (ℕ)

data Side : Set where
  north south east west middle : Side

data Port : Set where
  side : Side → Port          -- the midpoint of an edge, or the centre
  at   : Side → ℕ → Port      -- a percentage of the way along an edge (`at middle _` is the centre)

data VAlign : Set where
  top middle bottom : VAlign

data Align : Set where
  left centred right : Align
