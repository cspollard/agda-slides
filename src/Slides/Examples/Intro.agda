{-# OPTIONS --safe --without-K #-}

-- A small example deck, written with `do`-notation.

module Slides.Examples.Intro where

open import Slides.Core using (Body; Deck; Content; emph; codeSpan; link; inlineMath)
open import Slides.DSL
open import Data.List using (_∷_; [])
open import Slides.Math using (_≡_; _*_; _^_; _+_)

titleSlide : Body
titleSlide = do
  heading 1 "Slides in Agda"
  paragraph ("a " ∷ emph "free-monad" ∷ " DSL, checked by " ∷ codeSpan "agda" ∷ [])
  notes "Welcome everyone."

why : Body
why = do
  heading 2 "Why?"
  incremental ("typed decks" ∷ "verified export" ∷ "reusable components" ∷ [])
  displayMath ("E" ≡ "m" * "c" ^ 2)

compare : Body
compare = do
  heading 2 "Two columns"
  columns
    ( (do Content.heading 3 "Left"; Content.paragraph ("see " ∷ link "https://reveal.js" "reveal.js" ∷ []))
    ∷ (do Content.heading 3 "Right"; Content.paragraph ("inline " ∷ inlineMath ("a" ^ 2 + "b" ^ 2) ∷ " math" ∷ []))
    ∷ [] )
  box "Remark" (do Content.paragraph "Boxes hold content programs, too.")

demo : Deck
demo = do
  slide titleSlide
  slide why
  slideWith (background "#2a2a40") compare
  stack ( (do heading 2 "Details A"; paragraph "first")
        ∷ (do heading 2 "Details B"; code "agda" "id x = x")
        ∷ [] )
