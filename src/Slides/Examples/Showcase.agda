{-# OPTIONS --safe --without-K #-}

-- A deck that uses every feature, for end-to-end tests.

module Slides.Examples.Showcase where

open import Data.List using (_∷_; [])
open import Data.Product using (_,_)
open import Data.String using (String)

open import Slides.Core using (Deck; emph; strong; codeSpan; inlineMath; link)
open import Slides.DSL
open import Slides.Components
open import Slides.Diagram
open import Slides.Resources
import Slides.Math as M
open import Data.Nat using (ℕ)
open import Slides.Anim.Syntax using (Anim; Seg; hold; _⨾_)
open import Slides.Diagram.Syntax using (Dia; text)

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

-- a word that changes, one act per step
word : String → Anim ℕ (Seg ℕ)
word w = hold 1 (text 40 w defaultStyle)

showcase : Deck
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

  slide (do heading 2 "A diagram"
            diagram (record
              { name = "pipeline" ; width = 400 ; height = 100 ; percent = 70
              ; elements =
                  rect 10 25 110 50 defaultStyle
                ∷ label 65 50 16 "parse" defaultStyle
                ∷ arrow 120 50 190 50 defaultStyle
                ∷ rect 190 25 110 50 (filled "#355" defaultStyle)
                ∷ label 245 50 16 "render" defaultStyle
                ∷ [] })
            pause
            diagram (record
              { name = "result" ; width = 400 ; height = 60 ; percent = 40
              ; elements =
                  group (circle 30 30 20 (stroked "#e55" defaultStyle)
                       ∷ circle 80 30 20 (stroked "#5e5" defaultStyle)
                       ∷ [])
                ∷ label 200 30 16 "two circles" defaultStyle
                ∷ [] })
            placed 60 62 30 25 (Content.diagram (record
              { name = "inset" ; width = 100 ; height = 50 ; percent = 100
              ; elements = rect 5 5 90 40 (stroked "#e5e" defaultStyle) ∷ [] })))

  slide (do heading 2 "Animations"
            animate "steps" 40 100 ((word "one" ⨾ word "two") ∷ word "three" ∷ [])
            animateLoop "blink" 20 200 (word "tick" ⨾ word "tock"))

  slide (do heading 2 "Scripting"
            paragraph "The next line is written by JavaScript."
            mount "scripted"
            script "document.getElementById('scripted').textContent = 'script ran: ' + slide.querySelectorAll('h2').length + ' heading';")
