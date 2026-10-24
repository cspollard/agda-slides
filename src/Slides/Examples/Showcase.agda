{-# OPTIONS --safe --without-K #-}

-- A deck that uses every feature, for end-to-end tests.

module Slides.Examples.Showcase where

open import Data.List using (_∷_; [])
open import Data.Product using (_,_)

open import Slides.Core using (Deck; emph; strong; codeSpan; inlineMath; link)
open import Slides.DSL
open import Slides.Components
open import Slides.Capability.Placed
open import Slides.Resources
import Slides.Math as M

resources : Resources
resources = record
  { figures    = "plot.svg" ∷ []
  ; references =
      ("Knuth84" , "D. Knuth. The TeXbook. Addison-Wesley, 1984.")
    ∷ ("Moggi91" , "E. Moggi. Notions of computation and monads. 1991.")
    ∷ []
  }

open Checked resources

-- ∑ᵢ₌₀ⁿ i = n (n + 1) / 2
gauss : M.Math
gauss = M.sum (M.var "i" M.≡ 0) "n" "i" M.≡ M.frac ("n" M.* M.paren ("n" M.+ 1)) 2

-- e^{iπ} + 1 = 0
euler : M.Math
euler = (M.var "e" M.^ ("i" M.* M.greek M.pi)) M.+ 1 M.≡ 0

showcase : Deck Placed
showcase = do
  titleSlide "Showcase" "every feature of the DSL" "A. Speaker"

  slide (do heading 2 "Pause"
            paragraph "visible from the start"
            pause
            paragraph "appears on the first step"
            bullets ("and" ∷ "so" ∷ "do" ∷ "these" ∷ [])
            columns ( (do Content.paragraph "left column") ∷ (do Content.paragraph "right column") ∷ [])
            notes "Speaker notes stay out of the fragments.")

  slide (do heading 2 "Explicit fragments"
            incremental ("one" ∷ "two" ∷ "three" ∷ [])
            fragmentWith "fade-up" (Content.paragraph "and a styled one"))

  slide (do heading 2 "Typed math"
            displayMath gauss
            displayMath euler
            paragraph ("inline: " ∷ inlineMath (M.frac "a" "b") ∷ " and " ∷ inlineMath (M.sqrt 2) ∷ []))

  slide (do heading 2 "Marked-up text"
            paragraph ("plain, " ∷ emph "emphasis" ∷ ", " ∷ strong "strong" ∷ ", " ∷ codeSpan "code"
                       ∷ " and a " ∷ link "https://reveal.js" "link" ∷ []))

  slide (do heading 2 "Checked resources"
            figure "plot.svg" "A declared figure"
            paragraph ("Citations: " ∷ cite "Moggi91" ∷ " and " ∷ cite "Knuth84" ∷ []))

  slide (resultsTable "A table" ("feature" ∷ "status" ∷ [])
          (("pause" ∷ "done" ∷ []) ∷ ("math" ∷ "done" ∷ []) ∷ []))

  slideWith (background "#1b3a4b") (do heading 2 "A background"
                                       box "Box" (do Content.paragraph "boxes hold content"))

  stackWith (transition "zoom")
        ( (do heading 2 "Vertical A"; paragraph "press down")
        ∷ (do heading 2 "Vertical B"; code "agda" "id : {A : Set} → A → A\nid x = x")
        ∷ [] )

  slide (do heading 2 "References"
            bibliography)

  slide (do heading 2 "Placed boxes"
            placed 10 50 30 20 (Content.paragraph "a box at 10%, 50%")
            pause
            placed 60 50 30 20 (Content.paragraph "appears on the first step"))
