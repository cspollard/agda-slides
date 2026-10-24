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
    -- hooks for stylesheets and scripts, and finer presentation
    cls         : Maybe String   -- CSS class
    ident       : Maybe String   -- element id (unique in the deck)
    rx          : Maybe ℕ        -- corner radius of a rectangle
    dash        : Maybe String   -- stroke-dasharray, e.g. "6 4"
    opacity     : Maybe ℕ        -- percent
    anchor      : Maybe String   -- text-anchor of a label: start, middle, end

defaultStyle : Style
defaultStyle = record
  { stroke = nothing ; fill = nothing ; strokeWidth = nothing
  ; cls = nothing ; ident = nothing ; rx = nothing ; dash = nothing
  ; opacity = nothing ; anchor = nothing }

stroked : String → Style → Style
stroked c s = record s { stroke = just c }

filled : String → Style → Style
filled c s = record s { fill = just c }

thick : ℕ → Style → Style
thick n s = record s { strokeWidth = just n }

withClass : String → Style → Style
withClass c s = record s { cls = just c }

withId : String → Style → Style
withId i s = record s { ident = just i }

rounded : ℕ → Style → Style
rounded n s = record s { rx = just n }

dashed : String → Style → Style
dashed d s = record s { dash = just d }

-- opacity in percent
faded : ℕ → Style → Style
faded n s = record s { opacity = just n }

-- text-anchor of a label: "start" (the point is the left end), "middle", "end"
anchored : String → Style → Style
anchored a s = record s { anchor = just a }

data Element : Set where
  rect   : (x y w h : ℕ) → Style → Element
  circle : (cx cy r : ℕ) → Style → Element
  line   : (x₁ y₁ x₂ y₂ : ℕ) → Style → Element
  -- a line with an arrowhead at its end
  arrow  : (x₁ y₁ x₂ y₂ : ℕ) → Style → Element
  -- text centred at a point: position, font size, text, colour (the `fill`)
  label  : (x y size : ℕ) → String → Style → Element
  group  : List Element → Element
  -- an SVG path, `d` as in the `d` attribute (curves, polygons)
  path   : (d : String) → Style → Element

record Diagram : Set where
  field
    -- must be unique in the deck (used for the arrowhead's `id`)
    name     : String
    width    : ℕ
    height   : ℕ
    -- displayed width, in percent of the slide width
    percent  : ℕ
    elements : List Element

