{-# OPTIONS --safe --without-K #-}

-- An example deck built from components, with checked resources.

module Slides.Examples.Talk where

open import Data.List using (_∷_; [])
open import Data.Product using (_,_)

open import Slides.Core using (Deck)
open import Slides.DSL
open import Slides.Components
open import Slides.Resources

-- Everything the deck may refer to.  A typo in a name below is a type error.
resources : Resources
resources = record
  { figures    = "plot.svg" ∷ []
  ; references =
      ("Knuth84" , "D. Knuth. The TeXbook. Addison-Wesley, 1984.")
    ∷ ("Moggi91" , "E. Moggi. Notions of computation and monads. 1991.")
    ∷ []
  }

open Checked resources

talk : Deck
talk = do
  titleSlide "Verified slides" "free monads over containers" "A. Speaker"
  sectionSlide "Motivation"
  slide (withNotes "Say why." (incrementalBody "Why Agda?"
          ("types for structure" ∷ "proofs for export" ∷ [])))
  slide (do heading 2 "Monads"
            paragraph ("Effects as monads " ∷ cite "Moggi91" ∷ ", typeset with " ∷ cite "Knuth84" ∷ []))
  slide (resultsTable "Results" ("backend" ∷ "slides" ∷ [])
          (("reveal.js" ∷ "10" ∷ []) ∷ ("plain html" ∷ "0" ∷ []) ∷ []))
  slide (do heading 2 "A figure"
            figure "plot.svg" "A checked figure")
  slide (do heading 2 "Reveal step by step"
            fragment (Content.paragraph "first, a fragment")
            fragmentWith "fade-up" (Content.paragraph "then one that fades up"))
  slide (twoColumn "Compare" (Content.paragraph "left") (Content.paragraph "right"))
  slide (do heading 2 "References"
            bibliography)
