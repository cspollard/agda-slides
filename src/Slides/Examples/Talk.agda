{-# OPTIONS --safe --without-K #-}

-- An example deck built from components.

module Slides.Examples.Talk where

open import Data.List using (_∷_; [])

open import Slides.Core using (Deck)
open import Slides.DSL
open import Slides.Components

talk : Deck
talk = do
  titleSlide "Verified slides" "free monads over containers" "A. Speaker"
  sectionSlide "Motivation"
  slide (withNotes "Say why." (incrementalBody "Why Agda?"
          ("types for structure" ∷ "proofs for export" ∷ [])))
  slide (resultsTable "Results" ("backend" ∷ "slides" ∷ [])
          (("reveal.js" ∷ "10" ∷ []) ∷ ("plain html" ∷ "0" ∷ []) ∷ []))
  slide (do heading 2 "Reveal step by step"
            fragment (Content.paragraph "first, a fragment")
            fragmentWith "fade-up" (Content.paragraph "then one that fades up"))
  slide (twoColumn "Compare" (Content.paragraph "left") (Content.paragraph "right"))
