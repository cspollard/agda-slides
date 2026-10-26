{-# OPTIONS --safe --without-K #-}

-- A parametric animation: the data a backend ships instead of the frames.
--
-- An animation all of whose segments are templates (`Slides.Anim.Syntax.template`) is a
-- list of *symbolic layouts*, one per tick, laid out once in the free scalar
-- (`Slides.Diagram.Expr`): every coordinate is a formula in one variable per segment.
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
open import Slides.Diagram.Expr using (Expr)
open import Slides.Diagram.Euclid using (DExpr)
open import Slides.Anim.Track using (Piece)

record Param : Set where
  constructor param
  field
    -- the symbolic layout at each tick (the layout of the diagram running during
    -- `[k, k+1)`, over the variables below)
    ticks : List (Layout (Expr ℕ))
    -- for each segment (variable `i` is the `i`-th): the tick it starts at and the pieces of
    -- its track, in order
    segments : List (ℕ × List (Piece ℚ))

-- The same for an animation with *discrete* templates (`Slides.Anim.Syntax.discrete`,
-- `Slides.Diagram.Euclid`): the symbolic layouts are over `DExpr` and the page reads the
-- formulas in ℕ, at the whole tick `⌊τ⌋` (a discrete body has one frame per tick, and the
-- parameters it sees are whole: `units` of the track's sample).  Its own type, so that a
-- formula with floor division cannot be read as a continuous one by mistake.
record DParam : Set where
  constructor dparam
  field
    ticks    : List (Layout (DExpr ℕ))
    segments : List (ℕ × List (Piece ℚ))

-- what an animation can be shipped as
data AnyParam : Set where
  continuous : Param → AnyParam
  discrete   : DParam → AnyParam
