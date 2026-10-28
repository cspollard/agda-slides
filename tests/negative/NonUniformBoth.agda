{-# OPTIONS --safe --without-K #-}

-- Must NOT typecheck: phase 1 of the loop has an act of a different length than
-- phase 0, so the phases are not copies of one set of steps.

module NonUniformBoth where

open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)

open import Slides.Core using (ContentShape)
open import Slides.Anim.Syntax
open import Slides.Anim.Render using (renderBoth)
open import Slides.Diagram.Syntax
open import Slides.Diagram using (defaultStyle)

acts : ℕ → List (Anim)
acts zero = hold 1 (rectangle 1 1 defaultStyle) ∷ []
acts _    = hold 2 (rectangle 1 1 defaultStyle) ∷ []

bad : ContentShape
bad = renderBoth "bad" 100 100 2 acts
