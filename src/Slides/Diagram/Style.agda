{-# OPTIONS --safe --without-K #-}

-- How a drawing is styled: presentation attributes and hooks for stylesheets and scripts.
-- Colours are any CSS colour; unset means "the slide's text colour" for strokes and text and
-- no fill for shapes.  A style carries no coordinates, so it is untouched by a change of scalar.

module Slides.Diagram.Style where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.String using (String)

record Style : Set where
  constructor mkStyle
  field
    stroke fill cls ident dash anchor : Maybe String
    strokeWidth rx opacity            : Maybe ℕ   -- opacity in percent; rx a rectangle's corner
    -- `cls`: CSS class; `ident`: element id (unique in the deck); `dash`: stroke-dasharray;
    -- `anchor`: text-anchor of a label (start, middle, end)

defaultStyle : Style
defaultStyle = mkStyle nothing nothing nothing nothing nothing nothing nothing nothing nothing

stroked filled withClass withId dashed anchored : String → Style → Style
stroked c s  = record s { stroke = just c }
filled c s   = record s { fill = just c }
withClass c s = record s { cls = just c }
withId i s   = record s { ident = just i }
dashed d s   = record s { dash = just d }
anchored a s = record s { anchor = just a }

thick rounded faded : ℕ → Style → Style
thick n s   = record s { strokeWidth = just n }
rounded n s = record s { rx = just n }
faded n s   = record s { opacity = just n }
