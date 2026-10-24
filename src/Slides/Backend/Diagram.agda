{-# OPTIONS --safe --without-K #-}

-- HTML rendering of diagrams: inline SVG.
--
-- The shapes are parsnip's `Data.SVG` constructors; `line`, `text` and the
-- arrowhead marker use its `Sanitize` constructors directly.  A diagram is a
-- `<div class="diagram">` holding one `<svg>` with a `viewBox`; the arrowhead
-- marker's `id` is derived from the diagram's name.

module Slides.Backend.Diagram where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_)
open import Data.String using (String) renaming (_++_ to _++ˢ_)

open import Data.XML.AST using (XMLM)
open import Data.XML.Sanitize using (element; textElement)
import Data.SVG as SVG

open import Slides.Diagram
open import Slides.Backend.HTML using (hElement; padText)

private
  variable
    A : Set

  Attrs : Set
  Attrs = List (String × String)

  opt : String → Maybe String → Attrs
  opt k nothing  = []
  opt k (just v) = (k , v) ∷ []

  num : ℕ → String
  num = show

  _▹′_ : Maybe ℕ → (ℕ → String) → Maybe String
  nothing ▹′ f = nothing
  just n  ▹′ f = just (f n)

  -- hooks and presentation shared by every element
  commonAttrs : Style → Attrs
  commonAttrs s =
      opt "class" (Style.cls s)
    ++ opt "id" (Style.ident s)
    ++ opt "stroke-dasharray" (Style.dash s)
    ++ opt "opacity" (Style.opacity s ▹′ (λ n → num n ++ˢ "%"))

  -- Shapes are outlined in the text colour and unfilled unless styled.
  shapeAttrs : Style → Attrs
  shapeAttrs s =
      ("stroke" , maybeOr "currentColor" (Style.stroke s))
    ∷ ("fill" , maybeOr "none" (Style.fill s))
    ∷ opt "stroke-width" (Style.strokeWidth s ▹ num)
    ++ commonAttrs s
    where
      maybeOr : String → Maybe String → String
      maybeOr d nothing  = d
      maybeOr d (just v) = v
      _▹_ : Maybe ℕ → (ℕ → String) → Maybe String
      nothing ▹ f = nothing
      just n  ▹ f = just (f n)

  points : ℕ → ℕ → ℕ → ℕ → String
  points x₁ y₁ x₂ y₂ = num x₁ ++ˢ "," ++ˢ num y₁ ++ˢ " " ++ˢ num x₂ ++ˢ "," ++ˢ num y₂

  markerId : String → String
  markerId n = n ++ˢ "-arrow"

  lineEl : (x₁ y₁ x₂ y₂ : ℕ) → Attrs → XMLM A
  lineEl x₁ y₁ x₂ y₂ extra =
    element "line"
      ( ("x1" , num x₁) ∷ ("y1" , num y₁) ∷ ("x2" , num x₂) ∷ ("y2" , num y₂) ∷ extra ) []

  mutual
    renderElement : String → Element → XMLM A
    renderElement n (rect x y w h s)   =
      SVG.rect (num x) (num y) (num w) (num h) (opt "rx" (Style.rx s ▹′ num) ++ shapeAttrs s)
    renderElement n (circle x y r s)   = SVG.circle (num x) (num y) (num r) (shapeAttrs s)
    renderElement n (line a b c d s)   = lineEl a b c d (shapeAttrs s)
    renderElement n (arrow a b c d s)  =
      lineEl a b c d (shapeAttrs s ++ (("marker-end" , "url(#" ++ˢ markerId n ++ˢ ")") ∷ []))
    renderElement n (label x y sz t s) =
      textElement "text"
        ( ("x" , num x) ∷ ("y" , num y) ∷ ("font-size" , num sz)
        ∷ ("text-anchor" , maybeAnchor (Style.anchor s)) ∷ ("dominant-baseline" , "central")
        ∷ ("fill" , maybeOr (Style.fill s)) ∷ commonAttrs s)
        (padText t)
      where
        maybeOr : Maybe String → String
        maybeOr nothing  = "currentColor"
        maybeOr (just v) = v
        maybeAnchor : Maybe String → String
        maybeAnchor nothing  = "middle"
        maybeAnchor (just v) = v
    renderElement n (group es)         = SVG.g (commonAttrs defaultStyle) (renderElements n es)
    renderElement n (path d s)         = SVG.path d (shapeAttrs s)

    renderElements : String → List Element → List (XMLM A)
    renderElements n []       = []
    renderElements n (e ∷ es) = renderElement n e ∷ renderElements n es

  -- The arrowhead, drawn in the current colour.
  marker : String → XMLM A
  marker n =
    element "defs" []
      ( element "marker"
          ( ("id" , markerId n) ∷ ("viewBox" , "0 0 10 10") ∷ ("refX" , "9") ∷ ("refY" , "5")
          ∷ ("markerWidth" , "6") ∷ ("markerHeight" , "6") ∷ ("orient" , "auto") ∷ [])
          (SVG.path "M 0 0 L 10 5 L 0 10 z" (("fill" , "currentColor") ∷ []) ∷ [])
      ∷ [] )

  svgOf : Diagram → XMLM A
  svgOf d =
    SVG.svg
      ( ("viewBox" , "0 0 " ++ˢ num (Diagram.width d) ++ˢ " " ++ˢ num (Diagram.height d))
      ∷ ("style" , "width:" ++ˢ num (Diagram.percent d) ++ˢ "%;height:auto;")
      ∷ [] )
      (marker (Diagram.name d) ∷ renderElements (Diagram.name d) (Diagram.elements d))

renderDiagram : Diagram → XMLM A
renderDiagram d = hElement "div" (("class" , "diagram") ∷ ("id" , Diagram.name d) ∷ []) (svgOf d ∷ [])
