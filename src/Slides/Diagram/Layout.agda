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
-- for any `Ops S`, and, for decks, the same names at ℕ (so `layout : Dia ℕ →
-- Layout ℕ`).
--
-- Text is measured from a table of character widths (see
-- `Slides.Diagram.TextMetrics`): a `text` is `size * 3/2` high and as wide as
-- its characters, markup included, so centring, spacing and `paragraph`'s word
-- wrapping follow the actual text.

module Slides.Diagram.Layout where

open import Data.Fin using (zero; suc)
open import Data.List using (map)
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.String using (String)

open import Slides.Diagram using (Diagram)
open import Slides.Diagram.Draw using (Layout)
open import Slides.Diagram.Scalar using (Ops; natOps)
open import Slides.Diagram.Syntax public

-- The algebra, command by command (the geometry of each is in
-- `Slides.Diagram.Syntax`, its definition in `Slides.Diagram.Place`):
--
--   leaves            a frame with at most one drawing (a `Spacer` has none)
--   Beside Above      frames touch, sizes add in one direction and take the max
--                     in the other; the second child is drawn second
--   Atop              both centred in the larger frame; second drawn second
--   LabelAbove/Below  caption, diagram, room of the caption's height
--   Place Overlay     frame size declared by the caller, children at the corner
--                     or at (x, y); not centred
--   Named Connect     size and drawing of the child; a name, or one arrow
--
-- `layout d` is a `Layout`: its width and height are the frame of `d`.  The
-- origin of the frame is its top-left corner, y grows down.  `compile` halves
-- the positions (they are in half units) and makes the `Diagram`.
module LayoutWith {S : Set} (O : Ops S) where
  open Ops O using (toℕ)
  import Slides.Diagram.Place O as P

  layoutAlgebra : Algebra S (Layout S)
  layoutAlgebra (Rectangle w h s)   _ = P.rectangle w h s
  layoutAlgebra (Disc r s)          _ = P.disc r s
  layoutAlgebra (Segment w h s)     _ = P.segment w h s
  layoutAlgebra (Text pct size t s) _ = P.text pct size t s
  layoutAlgebra (Spacer w h)        _ = P.spacer w h
  layoutAlgebra (Beside al)         k = P.besideA al (k zero) (k (suc zero))
  layoutAlgebra (Above al)          k = P.aboveA al (k zero) (k (suc zero))
  layoutAlgebra Atop                k = P.atop (k zero) (k (suc zero))
  layoutAlgebra LabelAbove          k = P.labelAbove (k zero) (k (suc zero))
  layoutAlgebra LabelBelow          k = P.labelBelow (k zero) (k (suc zero))
  layoutAlgebra (Place w h x y)     k = P.place w h x y (k tt)
  layoutAlgebra (Overlay w h)       k = P.overlay w h (k zero) (k (suc zero))
  layoutAlgebra (Named n)           k = P.named n (k tt)
  layoutAlgebra (Connect a pa b pb s) k = P.connectP a pa b pb s (k tt)

  layout : Dia S → Layout S
  layout = fold layoutAlgebra

  -- `name` must be unique in the deck; `percent` is the displayed width.
  compile : (name : String) (percent : ℕ) → Dia S → Diagram
  compile n pct d = record
    { name = n ; width = toℕ (Layout.width l) ; height = toℕ (Layout.height l) ; percent = pct
    ; elements = map P.toElement (Layout.draws l) }
    where l = layout d

-- decks compute in ℕ
open LayoutWith natOps public
