{-# OPTIONS --safe --without-K #-}

-- A small example deck, written with `do`-notation.

module Slides.Examples.Intro where

open import Slides.Core using (Body; Deck; Content; emph; codeSpan; link; inlineMath)
open import Slides.DSL
open import Data.List using (_∷_; [])
open import Slides.Math using (_≡_; _*_; _^_; _+_)
open import Data.Nat using (ℕ)
open import Slides.Diagram using (defaultStyle; filled)
open import Slides.Diagram.Syntax using (rectangle; text; named)
open import Slides.Diagram.Notation using (↔; _∥_)
open import Slides.Diagram.Scalar using (natOps)
open import Slides.Anim.Syntax using (Anim; Seg; hold; tweenT; _⨾_)
open import Slides.Diagram.Ordered using (termOps; tO; lit)
import Slides.Diagram.Notation as N
open import Data.Unit using (⊤)
import Slides.Anim.Track as T
open import Data.Rational using (_/_)
open import Data.Integer using (+_)
open import Slides.Anim.Footprint using (parI)

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
  animate "mover" 60 400 (parI natOps mover counter ∷ [])
  notes "A free monad of Seq and Par over frames; each tick is a fragment."

-- a box sliding right with an ease-in-out curve: the position is a parameter
-- that follows an explicit track, sampled once per tick.  The body is a template, a
-- diagram whose sizes are formulas in the parameter `t`, so the page ships the formulas
-- and not the frames (`Slides.Anim.Param`).
private module E = N.NotationWith (termOps {⊤})

slide′ : Anim ℕ (Seg ℕ)
slide′ = tweenT 6 (+ 0 / 1) (+ 120 / 1) (T.Bezier (+ 40) (+ 0) (+ 20) (+ 100))
           (E.↔ tO ∥ named "slider" (rectangle (lit 40) (lit 30) (filled "#c96" defaultStyle)))

eased : Body
eased = do
  heading 2 "Easing"
  animate "slider" 60 150 (slide′ ∷ [])

-- two acts: each press plays one of them
acts : Body
acts = do
  heading 2 "Two acts"
  animate "acts" 40 100
    ( (hold 2 (text 24 "a" defaultStyle) ⨾ hold 1 (text 24 "b" defaultStyle))
    ∷ hold 2 (text 24 "c" defaultStyle)
    ∷ [] )

demo : Deck
demo = do
  slide titleSlide
  slide why
  slideWith (background "#2a2a40") compare
  slide animated
  slide eased
  slide acts
  stack ( (do heading 2 "Details A"; paragraph "first")
        ∷ (do heading 2 "Details B"; code "agda" "id x = x")
        ∷ [] )
