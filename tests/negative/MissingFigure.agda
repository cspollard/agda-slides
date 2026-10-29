{-# OPTIONS --safe --without-K #-}

-- Must NOT typecheck: "plto.svg" is not a declared figure.
-- EXPECT: Unsolved metas
-- Control: controls/FigureOk.agda.

module MissingFigure where

open import Data.List using (_∷_; [])

open import Slides.Deck.DSL

resources : Resources
resources = record { figures = "plot.svg" ∷ [] ; references = [] }

open Checked resources

typo : Body
typo = figure "plto.svg" "oops"
