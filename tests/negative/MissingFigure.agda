{-# OPTIONS --safe --without-K #-}

-- Must NOT typecheck: "plto.svg" is not a declared figure.

module MissingFigure where

open import Data.List using (_∷_; [])

open import Slides.Core using (Body; NoCap)
open import Slides.DSL
open import Slides.Resources

resources : Resources
resources = record { figures = "plot.svg" ∷ [] ; references = [] }

open Checked resources

typo : Body NoCap
typo = figure "plto.svg" "oops"
