{-# OPTIONS --safe --without-K #-}

-- A small example deck, written with `do`-notation.

module Slides.Examples.Intro where

open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ)
open import Data.String using (String)

open import Slides.Deck.Talk using (Talk)
open import Slides.Deck.DSL
open import Slides.Math using (_≡_; _*_; _^_; _+_)
open import Slides.Deck.Anim using (Anim; Leaf; lit; now; frame′; txt; tween; Linear; _⨾_; _∥_; ι; defaultStyle; filled)
open import Slides.Diagram.Syntax using (rectangle; spacer; beside; named)

titleSlide′ : Body
titleSlide′ = do
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
mover : Anim
mover = at 0 ⨾ at 60 ⨾ at 120
  where at : ℕ → Anim
        at x = frame′ 1 (beside (spacer (lit x) (lit 0)) (named "box" (rectangle (lit 40) (lit 30) (filled "#69c" defaultStyle))))

counter : Anim
counter = say "one" ⨾ say "two" ⨾ say "three"
  where say : String → Anim
        say t = frame′ 1 (named "caption" (txt 24 t defaultStyle))

animated : Body
animated = do
  heading 2 "Animation"
  animate "mover" 60 400 ((mover ∥ counter) ∷ [])
  notes "A scene of diagrams: the page evaluates its events."

-- a box sliding right: the position is a parameter that follows a driver, a term of Coupling
eased : Body
eased = do
  heading 2 "Easing"
  animate "slider" 60 150 (tween Linear (ι 0) (ι 120) (ι 6)
    (beside (spacer now (lit 0)) (named "slider" (rectangle (lit 40) (lit 30) (filled "#c96" defaultStyle)))) ∷ [])

-- two acts: each press plays one of them
acts : Body
acts = do
  heading 2 "Two acts"
  animate "acts" 40 100
    ( (frame′ 2 (txt 24 "a" defaultStyle) ⨾ frame′ 1 (txt 24 "b" defaultStyle))
    ∷ frame′ 2 (txt 24 "c" defaultStyle)
    ∷ [] )

demo : Talk
demo = do
  slide titleSlide′
  slide why
  slideWith (background "#2a2a40") compare
  slide animated
  slide eased
  slide acts
  stack (do heading 2 "Details A"; paragraph "first")
        ( (do heading 2 "Details B"; code "agda" "id x = x")
        ∷ [] )
