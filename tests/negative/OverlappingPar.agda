{-# OPTIONS --safe --without-K #-}

-- Must NOT typecheck: both sides of the `Par` declare the name "a".

module OverlappingPar where

open import Data.Nat using (ℕ)
open import Data.String using (String)

open import Slides.Anim.Syntax
open import Slides.Anim.Footprint
open import Slides.Diagram.Syntax
open import Slides.Diagram using (defaultStyle)

box : ℕ → String → Anim
box n s = hold n (named s (rectangle 1 1 defaultStyle))

bad : Anim
bad = parI (box 2 "a") (box 3 "a")
