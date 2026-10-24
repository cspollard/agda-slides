{-# OPTIONS --safe --without-K #-}

-- A small example deck, written with `do`-notation.

module Slides.Examples.Intro where

open import Slides.Core using (Body; Deck)
open import Slides.DSL
open import Data.List using (_∷_; [])

titleSlide : Body
titleSlide = do
  heading 1 "Slides in Agda"
  paragraph "a free-monad DSL"
  notes "Welcome everyone."

why : Body
why = do
  heading 2 "Why?"
  incremental ("typed decks" ∷ "verified export" ∷ "reusable components" ∷ [])
  displayMath "E = mc^2"

demo : Deck
demo = do
  slide titleSlide
  slide why
  stack ( (do heading 2 "Details A"; paragraph "first") ∷ (do heading 2 "Details B"; code "agda" "id x = x") ∷ [] )
