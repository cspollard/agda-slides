{-# OPTIONS --safe --without-K #-}

-- Rendering diagrams: the layout algebra.
--
-- `Slides.Diagram.Syntax` defines the language (a free monad on a container,
-- with smart constructors, re-exported here so that this is the one module a
-- deck opens); this module interprets it.  The carrier of the algebra is
-- `Slides.Diagram.Place.Layout`, a sized rectangle that draws itself at an
-- offset and carries named anchors, and `layout` is the catamorphism into it.
-- `compile` turns the result into a `Slides.Diagram.Diagram`, so the backends
-- and the stylesheets are unchanged.
--
-- Text is measured from a table of character widths (see
-- `Slides.Diagram.TextMetrics`): a `text` is `size * 3/2` high and as wide as
-- its characters, markup included, so centring, spacing and `paragraph`'s word
-- wrapping follow the actual text.

module Slides.Diagram.Layout where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ)
open import Data.String using (String)

open import Slides.Diagram using (Diagram)
open import Slides.Diagram.Syntax public
import Slides.Diagram.Place as P

private
  placePrim : PrimShape → P.Layout
  placePrim (Rectangle w h s)  = P.rectangle w h s
  placePrim (Disc r s)         = P.disc r s
  placePrim (Segment w h s)    = P.segment w h s
  placePrim (Text pct size t s) = P.text pct size t s
  placePrim (Spacer w h)       = P.spacer w h
  placePrim (Raw w h es)       = P.raw w h es

  placeConnective : (c : Connective) → (Fin (arity c) → P.Layout) → P.Layout
  placeConnective (Beside al g)     k = P.besideA al g (k zero) (k (suc zero))
  placeConnective (Above al g)      k = P.aboveA al g (k zero) (k (suc zero))
  placeConnective Atop              k = P.atop (k zero) (k (suc zero))
  placeConnective (Margin l t r b)  k = P.margin l t r b (k zero)
  placeConnective (MinWidth w)      k = P.minWidth w (k zero)
  placeConnective (TopAlign h)      k = P.topAligned h (k zero)
  placeConnective (LabelAbove g)    k = P.labelAbove g (k zero) (k (suc zero))
  placeConnective (LabelBelow g)    k = P.labelBelow g (k zero) (k (suc zero))

  placeAnnotation : Annotation → P.Layout → P.Layout
  placeAnnotation (Named n)               d = P.named n d
  placeAnnotation (Connect a pa b pb s)   d = P.connectP a pa b pb s d

layoutAlgebra : Algebra P.Layout
layoutAlgebra = record { prim = placePrim ; connective = placeConnective ; annotation = placeAnnotation }

layout : Dia → P.Layout
layout = fold layoutAlgebra

-- `name` must be unique in the deck; `percent` is the displayed width.
compile : (name : String) (percent : ℕ) → Dia → Diagram
compile n pct d = record
  { name = n ; width = P.width l ; height = P.height l ; percent = pct
  ; elements = P.render l 0 0 }
  where l = layout d
