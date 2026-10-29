{-# OPTIONS --safe --without-K #-}

-- A deck that uses every feature, for end-to-end tests.

module Slides.Examples.Showcase where

open import Data.List using (_∷_; [])
open import Data.Product using (_,_)
open import Data.Nat using (ℕ)
open import Data.String using (String)

open import Slides.Deck.Talk using (Talk)
open import Slides.Deck.DSL
import Slides.Math as M
open import Slides.Diagram.Style using (defaultStyle; filled; stroked)
open import Slides.Diagram.Syntax using (Dia; beside; framed; named; connect; disc; spacer)
import Slides.Diagram.Syntax as D
open import Slides.Deck.Anim using (Anim; frame′; txt; _⨾_)
open import Slides.Diagram.Geometry using (east; west)

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

box′ : String → Dia ℕ
box′ s = framed 110 50 defaultStyle (D.text (λ n → n) 100 16 s defaultStyle)

pipeline : Dia ℕ
pipeline = connect "parse" east "render" west defaultStyle
  (beside (named "parse" (box′ "parse")) (beside (spacer 70 0) (named "render" (framed 110 50 (filled "#355" defaultStyle) (D.text (λ n → n) 100 16 "render" defaultStyle)))))

twoCircles : Dia ℕ
twoCircles = beside (disc 20 (stroked "#e55" defaultStyle)) (disc 20 (stroked "#5e5" defaultStyle))

-- a word that changes, one act per step
word : String → Anim
word w = frame′ 1 (txt 40 w defaultStyle)

showcase : Talk
showcase = do
  titleSlide "Showcase" "every feature of the DSL" "A. Speaker"

  slide (do heading 2 "Pause"
            paragraph "visible from the start"
            pause
            paragraph "appears on the first step"
            bullets ("and" ∷ "so" ∷ "do" ∷ "these" ∷ [])
            columns ( Content.paragraph "left column" ∷ Content.paragraph "right column" ∷ [])
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
            figureWidth "plot.svg" 40 "The same figure at 40% of the width"
            paragraph ("Citations: " ∷ cite "Moggi91" ∷ " and " ∷ cite "Knuth84" ∷ []))

  slide (resultsTable "A table" ("feature" ∷ "status" ∷ [])
          (("pause" ∷ "done" ∷ []) ∷ ("math" ∷ "done" ∷ []) ∷ []))

  slideWith (background "#1b3a4b") (do heading 2 "A background"
                                       box "Box" (Content.paragraph "boxes hold content"))

  stackWith (transition "zoom") (do heading 2 "Vertical A"; paragraph "press down")
        ( (do heading 2 "Vertical B"; code "agda" "id : {A : Set} → A → A\nid x = x")
        ∷ [] )

  slide (do heading 2 "References"
            bibliography)

  slide (do heading 2 "Placed boxes"
            placed 10 50 30 20 (Content.paragraph "a box at 10%, 50%")
            pause
            placed 60 50 30 20 (Content.paragraph "appears on the first step"))

  slide (do heading 2 "A diagram"
            diagram "pipeline" 70 pipeline
            pause
            diagram "result" 40 twoCircles)

  slide (do heading 2 "Animations"
            animate "steps" 40 100 ((word "one" ⨾ word "two") ∷ word "three" ∷ [])
            animateLoop "blink" 20 200 (word "tick" ⨾ word "tock"))

  slide (do heading 2 "Scripting"
            paragraph "The next line is written by JavaScript."
            mount "scripted"
            script "document.getElementById('scripted').textContent = 'script ran: ' + slide.querySelectorAll('h2').length + ' heading';")
