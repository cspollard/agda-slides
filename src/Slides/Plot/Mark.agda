{-# OPTIONS --safe --without-K #-}

-- What a plot shows: marks in data coordinates (ℚ), each with a style and an optional legend entry.
-- A mark has no sub-terms, so a plot's content is a list of them (overlay is `++`).
--
--   line     a polyline through the points            scatter  a filled dot at each point
--   steps    a filled histogram: bin edges (n + 1) and heights (n), as one closed polygon
--   band     a filled region between a lower and an upper curve, (x, lo, hi) at each x
--   errors   a vertical bar with caps at each (x, y, err)
--   hline vline   a reference line across the whole plot
--   note     text at a data position
--   exact    the graph of a function ℚ → ℚ, sampled and drawn as a smooth curve (`Slides.Diagram.Curve`)

module Slides.Plot.Mark where

open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Product.Base using (_×_)
open import Data.Rational using (ℚ)
open import Data.String using (String)

open import Slides.Diagram.Style using (Style)

data Mark : Set where
  line scatter : Style → List (ℚ × ℚ) → Mark
  steps        : Style → List ℚ → List ℚ → Mark
  band         : Style → List (ℚ × ℚ × ℚ) → Mark
  errors       : Style → List (ℚ × ℚ × ℚ) → Mark
  hline vline  : Style → ℚ → Mark
  note         : ℚ → ℚ → String → Mark
  exact        : Style → (ℚ → ℚ) → Mark

record Series : Set where
  constructor series
  field
    mark   : Mark
    legend : Maybe String
