{-# OPTIONS --safe --without-K #-}

-- A small example deck, written with `do`-notation.

module Slides.Examples.Intro where

open import Slides.Core using (Body; Deck; Content; emph; codeSpan; link; inlineMath)
open import Slides.DSL
open import Data.List using (_∷_; [])
open import Slides.Math using (_≡_; _*_; _^_; _+_)
open import Data.Nat using (ℕ)
open import Slides.Diagram using (defaultStyle; filled)
open import Slides.Diagram.Syntax using (Dia; rectangle; text; named)
open import Slides.Diagram.Notation using (↔; _∥_)
open import Slides.Diagram.Scalar using (natOps)
open import Slides.Anim.Syntax using (Anim; Seg; hold; _⨾_)
open import Slides.Anim.Footprint using (parI; ⊤-witness)

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

-- a box moving right while a caption counts, together
mover : Anim ℕ (Seg ℕ)
mover = at 0 ⨾ at 60 ⨾ at 120
  where at : ℕ → Anim ℕ (Seg ℕ)
        at x = hold 1 (↔ x ∥ named "box" (rectangle 40 30 (filled "#69c" defaultStyle)))

counter : Anim ℕ (Seg ℕ)
counter = say "one" ⨾ say "two" ⨾ say "three"
  where say : _ → Anim ℕ (Seg ℕ)
        say t = hold 1 (named "caption" (text 24 t defaultStyle))

animated : Body
animated = do
  heading 2 "Animation"
  animate "mover" 60 (parI natOps mover counter)
  notes "A free monad of Seq and Par over frames; each tick is a fragment."

demo : Deck
demo = do
  slide titleSlide
  slide why
  slideWith (background "#2a2a40") compare
  slide animated
  stack ( (do heading 2 "Details A"; paragraph "first")
        ∷ (do heading 2 "Details B"; code "agda" "id x = x")
        ∷ [] )
