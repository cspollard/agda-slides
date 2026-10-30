{-# OPTIONS --safe --without-K #-}

-- The shared text tree (`Slides.Text`): sub/superscripts, styles and line breaks in prose and in
-- diagram labels, nested bullets.  Build with `make text`.

module Slides.Examples.TextDemo where

open import Data.Bool using (false)
open import Data.List using (_∷_; [])
open import Data.Maybe using (just; nothing)

open import Slides.Deck.Talk using (Talk)
open import Slides.Deck.DSL
open import Slides.Diagram.Style using (defaultStyle)
open import Slides.Diagram.Syntax using (textI; framed)
open import Slides.Text using (TextStyle; style; sub; sup; styled; br)
open import Slides.Deck.Content using (bullet; leaf)

red : TextStyle
red = style (just "#c33") (just "bold") nothing

demo : Talk
demo = slide (do
  heading 2 "One text tree"
  paragraph ("H" ∷ sub ("2" ∷ []) ∷ "O, E = mc" ∷ sup ("2" ∷ []) ∷ ", " ∷ styled red ("styled" ∷ []) ∷ br ∷ "and a second line" ∷ [])
  nested false
    ( bullet ("first" ∷ []) (leaf ("nested" ∷ []) ∷ bullet ("deeper" ∷ []) (leaf ("down here" ∷ []) ∷ []) ∷ [])
    ∷ leaf ("second" ∷ [])
    ∷ [])
  diagram "label" 40 (framed 160 80 defaultStyle (textI (λ n → n) 100 16
    ("x" ∷ sub ("i" ∷ []) ∷ br ∷ styled red ("styled" ∷ []) ∷ []) defaultStyle)))
