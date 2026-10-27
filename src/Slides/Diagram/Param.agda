{-# OPTIONS --safe --without-K #-}

-- A parametric animation: the data a backend ships instead of the frames.
--
-- An animation all of whose segments are templates (`Slides.Anim.Syntax.template`) is a
-- list of *symbolic layouts*, one per tick, laid out once in the free scalar
-- (`Slides.Diagram.Ordered`): every coordinate is a formula in one variable per segment.
-- Besides, the page needs each segment's *track* (`Slides.Anim.Track`: its pieces, with
-- durations, end values and easings) and the tick it starts at.  The page runs in real time
-- `τ` (`Slides.Anim.Continuous`): for `k ≤ τ < k+1` it evaluates the formulas of tick `k` at
-- the assignment `i ↦ (the sample at real time τ - start of segment i's track)`, in ℚ.  The
-- size is that of the formulas and the pieces, independent of the number of ticks.

module Slides.Diagram.Param where

open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Data.Rational using (ℚ)

open import Slides.Diagram.Draw using (Layout)
open import Slides.Diagram.Ordered using (OExpr)
open import Slides.Anim.Track using (Piece)

record Param : Set where
  constructor param
  field
    -- the symbolic layout at each tick (the layout of the diagram running during
    -- `[k, k+1)`, over the variables below)
    ticks : List (Layout (OExpr ℕ))
    -- for each segment (variable `i` is the `i`-th): the tick it starts at and the pieces of
    -- its track, in order
    segments : List (ℕ × List (Piece ℚ))
