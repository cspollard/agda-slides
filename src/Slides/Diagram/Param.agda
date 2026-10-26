{-# OPTIONS --safe --without-K #-}

-- A parametric animation: the data a backend ships instead of the frames.
--
-- An animation all of whose segments are templates (`Slides.Anim.Syntax.template`) is a
-- list of *symbolic layouts*, one per tick, laid out once in the free scalar
-- (`Slides.Diagram.Expr`): every coordinate is a formula in one variable per segment.
-- What the page needs besides is the assignment, for each segment, of its parameter on
-- each of its ticks.  The frame at tick `k` is the layout at the assignment
-- `v ↦ (parameter of segment v at tick k)`, which `Slides.Diagram.LayoutNatural` shows
-- is the layout of the instance (`layout-eval`, `layout-subst`).

module Slides.Diagram.Param where

open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)

open import Slides.Diagram.Draw using (Layout)
open import Slides.Diagram.Expr using (Expr)

record Param : Set where
  constructor param
  field
    -- the symbolic layout at each tick
    ticks : List (Layout (Expr ℕ))
    -- for each segment (variable `i` is the `i`-th): the tick it starts at and its
    -- parameter (in whole units) on each of its ticks
    segments : List (ℕ × List ℕ)
