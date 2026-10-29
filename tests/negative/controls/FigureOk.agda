{-# OPTIONS --safe --without-K #-}

-- Control for ../MissingFigure.agda: MUST typecheck (the figure is declared).

module FigureOk where

open import Data.List using (_∷_; [])

open import Slides.Deck.DSL

resources : Resources
resources = record { figures = "plot.svg" ∷ [] ; references = [] }

open Checked resources

ok : Body
ok = figure "plot.svg" "fine"
