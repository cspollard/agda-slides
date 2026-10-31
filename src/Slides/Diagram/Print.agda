{-# OPTIONS --safe --without-K #-}

-- Printing a layout as inline SVG: a map over the primitive list.
--
--   Layout S ──(map renderDraw over draws)──▶ <svg viewBox="0 0 w h"> <defs/marker> element* </svg>
--
-- A printer is told how to write a scalar (`Print`): `unit` a size, `pos` a position (stored in
-- half units, so `pos` halves it).  Shapes are parsnip's `Data.SVG` constructors, which sanitise
-- tag and attribute names; arrowheads use a marker whose id comes from the diagram's name.  A
-- label with markup is one `<text>` of `<tspan>`s shifted by whole user units (portable, unlike
-- `baseline-shift`).

module Slides.Diagram.Print where

open import Data.List using (List; []; _∷_; _++_; map; null; length)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; _*_; _/_; _∸_)
open import Data.Nat.Show using (show)
open import Data.Product.Base using (_×_; _,_)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Bool using (if_then_else_)
open import Data.String as Str using (toList)

open import Data.XML.AST using (XMLM)
open import Data.XML.Sanitize using (element; textElement)
import Data.SVG as SVG

open import Slides.Diagram.Style using (Style; defaultStyle)
open import Slides.Diagram.Draw
open import Slides.Text using (Inline; Text; Run; Sub; Sup; Styled; plainI; lines; TextStyle; style; noStyle)

-- how a scalar is written: a size, and a position given in half units
record Print (S : Set) : Set where
  field
    unit pos : S → String

-- ℕ: a position is halved, rounding down
natPrint : Print ℕ
natPrint = record { unit = show ; pos = λ x → show (x / 2) }

private
  variable A : Set

Attrs : Set
Attrs = List (String × String)

opt : String → Maybe String → Attrs
opt k nothing  = []
opt k (just v) = (k , v) ∷ []

padText : String → String
padText s = if null (toList s) then " " else s

-- hooks and presentation shared by every element
commonAttrs : Style → Attrs
commonAttrs s =
    opt "class" (Style.cls s) ++ opt "id" (Style.ident s) ++ opt "stroke-dasharray" (Style.dash s)
  ++ opt "opacity" (Maybe.map (λ n → show n ++ˢ "%") (Style.opacity s))

-- shapes are outlined in the text colour and unfilled unless styled
shapeAttrs : Style → Attrs
shapeAttrs s =
    ("stroke" , fromMaybe "currentColor" (Style.stroke s)) ∷ ("fill" , fromMaybe "none" (Style.fill s))
  ∷ opt "stroke-width" (Maybe.map show (Style.strokeWidth s)) ++ commonAttrs s

markerId : String → String
markerId n = n ++ˢ "-arrow"

translate : String → String → Attrs
translate x y = ("transform" , "translate(" ++ˢ x ++ˢ " " ++ˢ y ++ˢ ")") ∷ []

-- the presentation attributes of a style, the size being a percent of the label's
styleAttrs : ℕ → TextStyle → Attrs
styleAttrs sz (style c w z) = opt "fill" c ++ opt "font-weight" w ++ opt "font-size" (Maybe.map (λ n → show (sz * n / 100)) z)

-- a label's pieces: a subscript or superscript is shifted, anything else is written as its plain text
data Script : Set where
  sub sup plain : Script

scriptOf : Inline → Script
scriptOf Sub = sub
scriptOf Sup = sup
scriptOf _   = plain

styleOf : Inline → TextStyle
styleOf (Styled s) = s
styleOf _          = noStyle

undo : String → Maybe String
undo "" = nothing
undo d  = just d

-- `pending` is the vertical shift to undo at the next segment
tspanAttrs : ℕ → String → Script → Inline → Attrs
tspanAttrs sz pending sub   i = ("font-size" , show (sz * 7 / 10)) ∷ ("dy" , show (sz / 4)) ∷ []
tspanAttrs sz pending sup   i = ("font-size" , show (sz * 7 / 10)) ∷ ("dy" , "-" ++ˢ show (sz / 3)) ∷ []
tspanAttrs sz pending plain i = opt "dy" (undo pending) ++ styleAttrs sz (styleOf i)

tspan : ℕ → String → Script → Inline → XMLM A
tspan sz pending k i = textElement "tspan" (tspanAttrs sz pending k i) (padText (plainI i))

-- the shift the next segment undoes
shift : ℕ → Script → String
shift sz sub   = "-" ++ˢ show (sz / 4)
shift sz sup   = show (sz / 3)
shift sz plain = ""

tspans : ℕ → String → List Inline → List (XMLM A)
tspans sz pending []       = []
tspans sz pending (i ∷ ss) = tspan sz pending (scriptOf i) i ∷ tspans sz (shift sz (scriptOf i)) ss

-- how a label's lines are written
data Lines : Set where
  oneRun : String → Lines        -- a single plain run
  blank  : Lines
  oneRow : Text → Lines          -- one line with markup
  rowsOf : List Text → Lines     -- none or several

classify : List Text → Lines
classify ((Run u ∷ []) ∷ []) = oneRun u
classify ([] ∷ [])            = blank
classify (l ∷ [])             = oneRow l
classify ls                   = rowsOf ls

module _ {S : Set} (P : Print S) where
  open Print P

  lineEl : (x₁ y₁ x₂ y₂ : S) → Attrs → XMLM A
  lineEl x₁ y₁ x₂ y₂ extra =
    element "line" (("x1" , pos x₁) ∷ ("y1" , pos y₁) ∷ ("x2" , pos x₂) ∷ ("y2" , pos y₂) ∷ extra) []

  -- "x,y x,y ..." as SVG wants the points of a polyline
  points : List (S × S) → String
  points []             = ""
  points ((x , y) ∷ []) = pos x ++ˢ "," ++ˢ pos y
  points ((x , y) ∷ ps) = pos x ++ˢ "," ++ˢ pos y ++ˢ " " ++ˢ points ps

  -- a label: one `<text>` at a point; several lines are a `<tspan>` for each, the first raised so that the block is centred
  labelAttrs : S → S → ℕ → Style → Attrs
  labelAttrs x y sz s =
    ("x" , pos x) ∷ ("y" , pos y) ∷ ("font-size" , show sz)
    ∷ ("text-anchor" , fromMaybe "middle" (Style.anchor s)) ∷ ("dominant-baseline" , "central")
    ∷ ("fill" , fromMaybe "currentColor" (Style.fill s)) ∷ commonAttrs s

  labelRows : S → ℕ → String → List Text → List (XMLM A)
  labelRows x sz dy []       = []
  labelRows x sz dy (l ∷ ls) = element "tspan" (("x" , pos x) ∷ ("dy" , dy) ∷ []) (tspans sz "" l) ∷ labelRows x sz (show (sz * 3 / 2)) ls

  -- the first line is raised by half the height of the others
  firstDy : ℕ → List Text → String
  firstDy sz ls = "-" ++ˢ show ((length ls ∸ 1) * (sz * 3 / 2) / 2)

  labelEl : S → S → ℕ → Style → Lines → XMLM A
  labelEl x y sz s (oneRun u)  = textElement "text" (labelAttrs x y sz s) (padText u)
  labelEl x y sz s blank       = textElement "text" (labelAttrs x y sz s) " "
  labelEl x y sz s (oneRow l)  = element "text" (labelAttrs x y sz s) (tspans sz "" l)
  labelEl x y sz s (rowsOf ls) = element "text" (labelAttrs x y sz s) (labelRows x sz (firstDy sz ls) ls)

  mutual
    renderDraw : String → Draw S → XMLM A
    renderDraw n (rect x y w h s)  =
      SVG.rect (pos x) (pos y) (unit w) (unit h) (opt "rx" (Maybe.map show (Style.rx s)) ++ shapeAttrs s)
    renderDraw n (circle x y r s)  = SVG.circle (pos x) (pos y) (unit r) (shapeAttrs s)
    renderDraw n (ellipse x y a b s) =
      element "ellipse" (("cx" , pos x) ∷ ("cy" , pos y) ∷ ("rx" , unit a) ∷ ("ry" , unit b) ∷ shapeAttrs s) []
    renderDraw n (poly c ps s)     = (if c then SVG.polygon else SVG.polyline) (points ps) (shapeAttrs s)
    renderDraw n (line a b c d s)  = lineEl a b c d (shapeAttrs s)
    renderDraw n (arrow a b c d s) =
      lineEl a b c d (shapeAttrs s ++ (("marker-end" , "url(#" ++ˢ markerId n ++ˢ ")") ∷ []))
    renderDraw n (label x y sz t s) = labelEl x y sz s (classify (lines t))
    renderDraw n (path x y d s)    = SVG.path d (translate (pos x) (pos y) ++ shapeAttrs s)

  -- the arrowhead, drawn in the current colour
  markerAttrs : String → Attrs
  markerAttrs n =
    ("id" , markerId n) ∷ ("viewBox" , "0 0 10 10") ∷ ("refX" , "9") ∷ ("refY" , "5")
    ∷ ("markerWidth" , "6") ∷ ("markerHeight" , "6") ∷ ("orient" , "auto") ∷ []

  arrowhead : String → XMLM A
  arrowhead n = element "marker" (markerAttrs n) (SVG.path "M 0 0 L 10 5 L 0 10 z" (("fill" , "currentColor") ∷ []) ∷ [])

  marker : String → XMLM A
  marker n = element "defs" [] (arrowhead n ∷ [])

  -- the layout as an `<svg>` of the given name (unique in the deck), shown `percent` wide
  svgAttrs : ℕ → Layout S → Attrs
  svgAttrs percent l =
    ("viewBox" , "0 0 " ++ˢ unit (Layout.width l) ++ˢ " " ++ˢ unit (Layout.height l))
    ∷ ("style" , "width:" ++ˢ show percent ++ˢ "%;height:auto;") ∷ []

  renderSVG : String → ℕ → Layout S → XMLM A
  renderSVG n percent l = SVG.svg (svgAttrs percent l) (marker n ∷ map (renderDraw n) (Layout.draws l))
