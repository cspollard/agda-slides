{-# OPTIONS --safe --without-K #-}

-- The vocabulary of placement shared by the diagram syntax and its layout
-- interpretation: the points on a box that arrows attach to, and alignments.
-- (Boxes and the arithmetic on them are in `Slides.Diagram.Draw` and
-- `Slides.Diagram.Place`, which are parametrised by a scalar.)

module Slides.Diagram.Geometry where

open import Data.Nat using (ℕ)

-- The points of a box that a connection can attach to: the middle of each
-- edge, and the centre.  (`middle` is also an alignment, see `VAlign`; the
-- two live in different types.)
--
--          north
--       +----N----+
--       |         |
--  west W    M    E east        N, S, E, W: midpoints of the edges
--       |         |             M: the centre of the box
--       +----S----+
--          south
data Side : Set where
  north south east west middle : Side

-- A point along a side, in percent from the left (north, south) or the top
-- (east, west): `at north 40` is two fifths of the way along the top edge.
-- It spreads several connections over one edge.  Percentages are counted along
-- the edge from its start, so west and east edges count from the top.
-- `at middle p` is the centre, whatever `p` is.
--
--        at north 40
--       +----*--------+     the stars are `at north 40` (40% from the
--       *  at west 25 |     left of the top edge) and `at west 25`
--       |             |     (25% down the left edge); `side north` is
--       |             |     `at north 50`
--       +-------------+
data Port : Set where
  side : Side → Port
  at   : Side → ℕ → Port

-- Alignment of a row (vertically) and of a column (horizontally): where the
-- smaller of two neighbours sits in the extra room.  `VAlign` is for `Beside`
-- (children side by side, so the heights differ), `Align` for `Above`
-- (children stacked, so the widths differ).  Pictures: `Slides.Diagram.Syntax`.
--
--   VAlign:  top      the tops line up
--            middle   centred vertically (the default of `∥`)
--            bottom   the bottoms line up
--   Align:   left     the left edges line up
--            centred  centred horizontally (the default of `═`)
--            right    the right edges line up
data VAlign : Set where
  top middle bottom : VAlign

data Align : Set where
  left centred right : Align
