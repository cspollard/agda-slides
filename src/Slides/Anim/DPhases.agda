{-# OPTIONS --safe --without-K #-}

-- What the backend ships for a discrete parametric animation, as data.  As
-- `Slides.Anim.Phases`, with the formulas of the numbers read in ℕ.
--
-- The shipped data are the same `Elem`s and phases as for continuous templates (`Elem`, `runs` and
-- the grouping are shared: nothing in them depends on how a formula is read).  What differs is the
-- encoding of a number (`encD`, which folds closed subformulas in ℕ, with no side condition).
-- What it means is `Slides.Anim.DPhases.Properties.Discrete`.

module Slides.Anim.DPhases where

open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)

open import Slides.Diagram.Draw using (Draw; Layout)
open import Slides.Diagram.Euclid using (DExpr; evalD; natD)
open import Slides.Anim.Formula
open import Slides.Anim.Phases

-- the formula of a number: positions are halved
slotFD : Kind × DExpr ℕ → Formula
slotFD (pos  , e) = half (encD e)
slotFD (size , e) = encD e

encodeDrawD : Draw (DExpr ℕ) → Elem
encodeDrawD = encodeWith slotFD (evalD natD (λ _ → 0))

phasesOfD : List (Layout (DExpr ℕ)) → List (ℕ × List Elem)
phasesOfD = phasesWith slotFD (evalD natD (λ _ → 0))
