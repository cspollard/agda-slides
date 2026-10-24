{-# OPTIONS --safe --without-K #-}

-- Small vector diagrams.
--
-- A diagram is a list of elements on a canvas of integer coordinates
-- (`width × height` units, scaled to `percent` of the slide width).  The AST
-- is backend-independent: the HTML backends print it as inline SVG (see
-- `Slides.Backend.Diagram`); a LaTeX backend could print TikZ.

module Slides.Diagram where

open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.String using (String)

-- Colours are any CSS colour; unset means "the slide's text colour" for
-- strokes and text, and no fill for shapes.
record Style : Set where
  field
    stroke      : Maybe String
    fill        : Maybe String
    strokeWidth : Maybe ℕ

defaultStyle : Style
defaultStyle = record { stroke = nothing ; fill = nothing ; strokeWidth = nothing }

stroked : String → Style → Style
stroked c s = record s { stroke = just c }

filled : String → Style → Style
filled c s = record s { fill = just c }

thick : ℕ → Style → Style
thick n s = record s { strokeWidth = just n }

data Element : Set where
  rect   : (x y w h : ℕ) → Style → Element
  circle : (cx cy r : ℕ) → Style → Element
  line   : (x₁ y₁ x₂ y₂ : ℕ) → Style → Element
  -- a line with an arrowhead at its end
  arrow  : (x₁ y₁ x₂ y₂ : ℕ) → Style → Element
  -- text centred at a point: position, font size, text, colour (the `fill`)
  label  : (x y size : ℕ) → String → Style → Element
  group  : List Element → Element

record Diagram : Set where
  field
    -- must be unique in the deck (used for the arrowhead's `id`)
    name     : String
    width    : ℕ
    height   : ℕ
    -- displayed width, in percent of the slide width
    percent  : ℕ
    elements : List Element

