{-# OPTIONS --safe --without-K #-}

-- Rendering diagrams: the layout algebra.
--
-- `Slides.Diagram.Syntax` defines the language (a free monad on a container,
-- with smart constructors, re-exported here so that this is the one module a
-- deck opens); this module interprets it.  The carrier of the algebra is
-- `Slides.Diagram.Draw.Layout`, a sized rectangle with its drawing commands and
-- named anchors, and `layout` is the catamorphism into it.  `compile` turns the
-- result into a `Slides.Diagram.Diagram`, so the backends and the stylesheets
-- are unchanged.
--
-- The layout is computed in a scalar (`Slides.Diagram.Scalar`): `LayoutWith O`
-- for any `Ops S`, and, for decks, the same names at ℕ.
--
-- Text is measured from a table of character widths (see
-- `Slides.Diagram.TextMetrics`): a `text` is `size * 3/2` high and as wide as
-- its characters, markup included, so centring, spacing and `paragraph`'s word
-- wrapping follow the actual text.

module Slides.Diagram.Layout where

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (map)
open import Data.Nat using (ℕ)
open import Data.String using (String)

open import Slides.Diagram using (Diagram)
open import Slides.Diagram.Draw using (Layout)
open import Slides.Diagram.Scalar using (Ops; natOps)
open import Slides.Diagram.Syntax public

module LayoutWith {S : Set} (O : Ops S) where
  open Ops O using (fromℕ; toℕ)
  import Slides.Diagram.Place O as P

  private
    placePrim : PrimShape → Layout S
    placePrim (Rectangle w h s)   = P.rectangle (fromℕ w) (fromℕ h) s
    placePrim (Disc r s)          = P.disc (fromℕ r) s
    placePrim (Segment w h s)     = P.segment (fromℕ w) (fromℕ h) s
    placePrim (Text pct size t s) = P.text pct size t s
    placePrim (Spacer w h)        = P.spacer (fromℕ w) (fromℕ h)
    placePrim (Raw w h es)        = P.raw (fromℕ w) (fromℕ h) es

    placeConnective : (c : Connective) → (Fin (arity c) → Layout S) → Layout S
    placeConnective (Beside al g)     k = P.besideA al (fromℕ g) (k zero) (k (suc zero))
    placeConnective (Above al g)      k = P.aboveA al (fromℕ g) (k zero) (k (suc zero))
    placeConnective Atop              k = P.atop (k zero) (k (suc zero))
    placeConnective (Margin l t r b)  k = P.margin (fromℕ l) (fromℕ t) (fromℕ r) (fromℕ b) (k zero)
    placeConnective (MinWidth w)      k = P.minWidth (fromℕ w) (k zero)
    placeConnective (TopAlign h)      k = P.topAligned (fromℕ h) (k zero)
    placeConnective (LabelAbove g)    k = P.labelAbove (fromℕ g) (k zero) (k (suc zero))
    placeConnective (LabelBelow g)    k = P.labelBelow (fromℕ g) (k zero) (k (suc zero))

    placeAnnotation : Annotation → Layout S → Layout S
    placeAnnotation (Named n)               d = P.named n d
    placeAnnotation (Connect a pa b pb s)   d = P.connectP a pa b pb s d

  layoutAlgebra : Algebra (Layout S)
  layoutAlgebra = record { prim = placePrim ; connective = placeConnective ; annotation = placeAnnotation }

  layout : Dia → Layout S
  layout = fold layoutAlgebra

  -- `name` must be unique in the deck; `percent` is the displayed width.
  compile : (name : String) (percent : ℕ) → Dia → Diagram
  compile n pct d = record
    { name = n ; width = toℕ (Layout.width l) ; height = toℕ (Layout.height l) ; percent = pct
    ; elements = map P.toElement (Layout.draws l) }
    where l = layout d

-- decks compute in ℕ
open LayoutWith natOps public
