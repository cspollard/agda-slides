{-# OPTIONS --safe --without-K #-}

-- A small deck with named slides, for the label navigation test: not part of the goldens.
-- Slides are, from 0: intro, details, an unnamed one, the stack `more` (two slides), end.

module Slides.Examples.Labels where

open import Data.List using (_∷_; [])

open import Slides.Deck.Talk using (Talk)
open import Slides.Deck.DSL

labels : Talk
labels = do
  slideAs "intro" (do heading 1 "Intro"; paragraph "the first slide")
  slideAs "details" (do heading 2 "Details"
                        paragraph "visible from the start"
                        pause
                        paragraph "after one step")
  slide (do heading 2 "Unnamed"; paragraph "reachable by number only")
  stackWith (labelled "more" (background "#000")) (do heading 2 "More A"; paragraph "top of the stack")
    ( (do heading 2 "More B"; paragraph "below it") ∷ [] )
  slideAs "end" (do heading 2 "End"; paragraph "the last slide")
