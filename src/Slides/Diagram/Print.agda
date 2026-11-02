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

open import Data.List using (List; []; _∷_; _++_; map; null; length; foldr; concatMap; reverse)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; _+_; _*_; _/_; _∸_; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product.Base using (_×_; _,_)
open import Data.String using (String; fromList; toList; _==_) renaming (_++_ to _++ˢ_)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Char using (Char; toℕ)

open import Data.XML.AST using (XMLM)
open import Data.XML.Sanitize using (element; textElement)
import Data.SVG as SVG

open import Slides.Diagram.Style using (Style; defaultStyle)
open import Slides.Diagram.Draw
open import Slides.Math using (toLaTeX)
open import Slides.Text using (Inline; Text; Run; Sub; Sup; Styled; MathI; plainI; lines; TextStyle; style; noStyle)

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

-- preserve leading and trailing spaces at `<tspan>` boundaries
padChars : List Char → List Char
padChars []         = ' ' ∷ []
padChars (' ' ∷ cs) = '\xA0' ∷ end cs
  where end : List Char → List Char
        end []         = []
        end (' ' ∷ []) = '\xA0' ∷ []
        end (d ∷ r)    = d ∷ end r
padChars (c ∷ cs)   = c ∷ end cs
  where end : List Char → List Char
        end []         = []
        end (' ' ∷ []) = '\xA0' ∷ []
        end (d ∷ r)    = d ∷ end r

padSpan : String → String
padSpan s = fromList (padChars (toList s))

rotateAttr : String → String → Maybe String → Attrs
rotateAttr x y nothing  = []
rotateAttr x y (just a) = ("transform" , "rotate(" ++ˢ a ++ˢ " " ++ˢ x ++ˢ " " ++ˢ y ++ˢ ")") ∷ []

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

-- a label's pieces: a subscript or superscript is shifted, anything else is written as its plain text;
-- `$...$` (or `inlineMath`) is split into upright (`KaTeX_Main`) and italic (`KaTeX_Math`) runs
data Script : Set where
  sub sup plain : Script

data MathFont : Set where
  noMath mathRm mathIt : MathFont

record Seg : Set where
  constructor seg
  field
    scr   : Script
    mfont : MathFont
    tsty  : TextStyle
    body  : String

private
  inRange : ℕ → ℕ → Char → Bool
  inRange lo hi c = not (toℕ c <ᵇ lo) ∧ not (hi <ᵇ toℕ c)

  isLetter : Char → Bool
  isLetter c = inRange 65 90 c ∨ inRange 97 122 c

  isGreekLower : Char → Bool
  isGreekLower c =
    inRange 945 969 c ∨ (toℕ c ≡ᵇ 977) ∨ (toℕ c ≡ᵇ 981)
    ∨ (toℕ c ≡ᵇ 982) ∨ (toℕ c ≡ᵇ 1013) ∨ (toℕ c ≡ᵇ 8467)

  isMathItalic : Char → Bool
  isMathItalic c = isLetter c ∨ isGreekLower c

  isRmCmd : String → Bool
  isRmCmd s = (s == "mathrm") ∨ (s == "text") ∨ (s == "rm") ∨ (s == "operatorname")

  greekTable : List (String × Char)
  greekTable =
      ("alpha" , 'α') ∷ ("beta" , 'β') ∷ ("gamma" , 'γ') ∷ ("delta" , 'δ')
    ∷ ("epsilon" , 'ϵ') ∷ ("varepsilon" , 'ε') ∷ ("zeta" , 'ζ') ∷ ("eta" , 'η')
    ∷ ("theta" , 'θ') ∷ ("vartheta" , 'ϑ') ∷ ("iota" , 'ι') ∷ ("kappa" , 'κ')
    ∷ ("lambda" , 'λ') ∷ ("mu" , 'μ') ∷ ("nu" , 'ν') ∷ ("xi" , 'ξ')
    ∷ ("pi" , 'π') ∷ ("rho" , 'ρ') ∷ ("sigma" , 'σ') ∷ ("tau" , 'τ')
    ∷ ("upsilon" , 'υ') ∷ ("phi" , 'ϕ') ∷ ("varphi" , 'φ') ∷ ("chi" , 'χ')
    ∷ ("psi" , 'ψ') ∷ ("omega" , 'ω') ∷ ("ell" , 'ℓ') ∷ []

  rmTable : List (String × String)
  rmTable =
      ("Gamma" , "Γ") ∷ ("Delta" , "Δ") ∷ ("Theta" , "Θ") ∷ ("Lambda" , "Λ")
    ∷ ("Xi" , "Ξ") ∷ ("Pi" , "Π") ∷ ("Sigma" , "Σ") ∷ ("Upsilon" , "Υ")
    ∷ ("Phi" , "Φ") ∷ ("Psi" , "Ψ") ∷ ("Omega" , "Ω")
    ∷ ("pm" , "±") ∷ ("mp" , "∓") ∷ ("times" , "×") ∷ ("cdot" , "·") ∷ ("div" , "÷")
    ∷ ("le" , "≤") ∷ ("leq" , "≤") ∷ ("ge" , "≥") ∷ ("geq" , "≥")
    ∷ ("ne" , "≠") ∷ ("neq" , "≠") ∷ ("approx" , "≈") ∷ ("equiv" , "≡")
    ∷ ("sim" , "∼") ∷ ("propto" , "∝") ∷ ("to" , "→") ∷ ("rightarrow" , "→")
    ∷ ("leftarrow" , "←") ∷ ("Rightarrow" , "⇒") ∷ ("infty" , "∞")
    ∷ ("partial" , "∂") ∷ ("nabla" , "∇")
    ∷ ("sin" , "sin") ∷ ("cos" , "cos") ∷ ("tan" , "tan") ∷ ("exp" , "exp")
    ∷ ("ln" , "ln") ∷ ("log" , "log") ∷ ("min" , "min") ∷ ("max" , "max")
    ∷ ("left" , "") ∷ ("right" , "") ∷ []

  findGreek : String → List (String × Char) → Maybe Char
  findGreek k []             = nothing
  findGreek k ((m , c) ∷ ms) = if k == m then just c else findGreek k ms

  findRm : String → List (String × String) → Maybe String
  findRm k []             = nothing
  findRm k ((m , v) ∷ ms) = if k == m then just v else findRm k ms

  macroToks : Script → String → List (Script × MathFont × Char)
  macroToks sc k with findGreek k greekTable
  ... | just c  = (sc , mathIt , c) ∷ []
  ... | nothing with findRm k rmTable
  ...   | just v  = map (λ c → sc , mathRm , c) (toList v)
  ...   | nothing = map (λ c → sc , mathRm , c) (toList k)

  escToks : Script → Char → List (Script × MathFont × Char)
  escToks sc ',' = (sc , mathRm , ' ') ∷ []
  escToks sc ';' = (sc , mathRm , ' ') ∷ []
  escToks sc ':' = (sc , mathRm , ' ') ∷ []
  escToks sc ' ' = (sc , mathRm , ' ') ∷ []
  escToks sc '!' = []
  escToks sc c   = (sc , mathRm , c) ∷ []

  onChar : Script → Bool → Bool → Char → List (Script × MathFont × Char) × Script × Bool × Bool × Maybe (List Char)
  onChar sc br rm '\\'        = [] , sc , br , rm , just []
  onChar sc br rm '_'         = [] , sub , false , rm , nothing
  onChar sc br rm '^'         = [] , sup , false , rm , nothing
  onChar plain br rm '{'      = [] , plain , false , rm , nothing
  onChar sc    br rm '{'      = [] , sc , true , rm , nothing
  onChar sc br true  '}'      = [] , (if br then sc else plain) , br , false , nothing
  onChar sc br false '}'      = [] , plain , false , false , nothing
  onChar sc br rm '-'         = ((sc , mathRm , '−') ∷ []) , (if br ∨ rm then sc else plain) , br , rm , nothing
  onChar sc br rm c           =
    let mf = if rm then mathRm else if isMathItalic c then mathIt else mathRm
    in ((sc , mf , c) ∷ []) , (if br ∨ rm then sc else plain) , br , rm , nothing

  lexMath : Script → Bool → Bool → Maybe (List Char) → List Char → List (Script × MathFont × Char)
  lexMath sc br rm nothing          []       = []
  lexMath sc br rm (just [])        []       = []
  lexMath sc br rm (just (a ∷ acc)) []       = macroToks sc (fromList (reverse (a ∷ acc)))
  lexMath sc br rm nothing          (c ∷ cs) with onChar sc br rm c
  ... | ts , sc′ , br′ , rm′ , cmd′          = ts ++ lexMath sc′ br′ rm′ cmd′ cs
  lexMath sc br rm (just [])        (c ∷ cs) =
    if isLetter c
    then lexMath sc br rm (just (c ∷ [])) cs
    else escToks sc c ++ lexMath (if br ∨ rm then sc else plain) br rm nothing cs
  lexMath sc br rm (just (a ∷ acc)) (c ∷ cs) =
    if isLetter c
    then lexMath sc br rm (just (c ∷ a ∷ acc)) cs
    else let name = fromList (reverse (a ∷ acc)) in
         if isRmCmd name ∧ (toℕ c ≡ᵇ 123)
         then lexMath sc br true nothing cs
         else let sc₁ = if br ∨ rm then sc else plain
                  r   = onChar sc₁ br rm c
              in macroToks sc name ++ Data.Product.Base.proj₁ r
                 ++ lexMath (Data.Product.Base.proj₁ (Data.Product.Base.proj₂ r))
                            (Data.Product.Base.proj₁ (Data.Product.Base.proj₂ (Data.Product.Base.proj₂ r)))
                            (Data.Product.Base.proj₁ (Data.Product.Base.proj₂ (Data.Product.Base.proj₂ (Data.Product.Base.proj₂ r))))
                            (Data.Product.Base.proj₂ (Data.Product.Base.proj₂ (Data.Product.Base.proj₂ (Data.Product.Base.proj₂ r))))
                            cs

  eqMF : MathFont → MathFont → Bool
  eqMF noMath noMath = true
  eqMF mathRm mathRm = true
  eqMF mathIt mathIt = true
  eqMF _      _      = false

  sameMode : Script → MathFont → Script → MathFont → Bool
  sameMode sub   a sub   b = eqMF a b
  sameMode sup   a sup   b = eqMF a b
  sameMode plain a plain b = eqMF a b
  sameMode _     _ _     _ = false

  addChar : Script × MathFont × Char → List Seg → List Seg
  addChar (sc , mf , c) [] = seg sc mf noStyle (fromList (c ∷ [])) ∷ []
  addChar (sc , mf , c) (seg sc′ mf′ st s ∷ gs) =
    if sameMode sc mf sc′ mf′
    then seg sc mf st (fromList (c ∷ toList s)) ∷ gs
    else seg sc mf noStyle (fromList (c ∷ [])) ∷ seg sc′ mf′ st s ∷ gs

mathSegs : String → List Seg
mathSegs s = foldr addChar [] (lexMath plain false false nothing (toList s))

inlineSeg : Inline → List Seg
inlineSeg (MathI m)    = mathSegs (toLaTeX m)
inlineSeg i@Sub        = seg sub   noMath noStyle (plainI i) ∷ []
inlineSeg i@Sup        = seg sup   noMath noStyle (plainI i) ∷ []
inlineSeg i@(Styled s) = seg plain noMath s       (plainI i) ∷ []
inlineSeg i            = seg plain noMath noStyle (plainI i) ∷ []

inlineSegs : List Inline → List Seg
inlineSegs = concatMap inlineSeg

mathFontAttrs : MathFont → Attrs
mathFontAttrs noMath = []
mathFontAttrs mathRm = ("font-family" , "KaTeX_Main, STIX Two Text, Times New Roman, serif") ∷ []
mathFontAttrs mathIt = ("font-family" , "KaTeX_Math, STIX Two Text, Times New Roman, serif") ∷ ("font-style" , "italic") ∷ []

dyBetween : ℕ → Script → Script → Maybe String
dyBetween sz plain plain = nothing
dyBetween sz plain sub   = just (show (sz / 4))
dyBetween sz plain sup   = just ("-" ++ˢ show (sz / 3))
dyBetween sz sub   plain = just ("-" ++ˢ show (sz / 4))
dyBetween sz sub   sub   = nothing
dyBetween sz sub   sup   = just ("-" ++ˢ show (sz / 4 + sz / 3))
dyBetween sz sup   plain = just (show (sz / 3))
dyBetween sz sup   sub   = just (show (sz / 3 + sz / 4))
dyBetween sz sup   sup   = nothing

segAttrs : ℕ → Script → Seg → Attrs
segAttrs sz prev (seg sub   mf st _) = ("font-size" , show (sz * 7 / 10)) ∷ opt "dy" (dyBetween sz prev sub) ++ mathFontAttrs mf ++ styleAttrs sz st
segAttrs sz prev (seg sup   mf st _) = ("font-size" , show (sz * 7 / 10)) ∷ opt "dy" (dyBetween sz prev sup) ++ mathFontAttrs mf ++ styleAttrs sz st
segAttrs sz prev (seg plain mf st _) = opt "dy" (dyBetween sz prev plain) ++ mathFontAttrs mf ++ styleAttrs sz st

tspanSeg : ℕ → Script → Seg → XMLM A
tspanSeg sz prev g = textElement "tspan" (segAttrs sz prev g) (padSpan (Seg.body g))

tspanSegs : ℕ → Script → List Seg → List (XMLM A)
tspanSegs sz prev []       = []
tspanSegs sz prev (g ∷ gs) = tspanSeg sz prev g ∷ tspanSegs sz (Seg.scr g) gs

tspans : ℕ → List Inline → List (XMLM A)
tspans sz is = tspanSegs sz plain (inlineSegs is)

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
    ∷ ("fill" , fromMaybe "currentColor" (Style.fill s))
    ∷ rotateAttr (pos x) (pos y) (Style.rotate s) ++ commonAttrs s

  labelRows : S → ℕ → String → List Text → List (XMLM A)
  labelRows x sz dy []       = []
  labelRows x sz dy (l ∷ ls) = element "tspan" (("x" , pos x) ∷ ("dy" , dy) ∷ []) (tspans sz l) ∷ labelRows x sz (show (sz * 3 / 2)) ls

  -- the first line is raised by half the height of the others
  firstDy : ℕ → List Text → String
  firstDy sz ls = "-" ++ˢ show ((length ls ∸ 1) * (sz * 3 / 2) / 2)

  labelEl : S → S → ℕ → Style → Lines → XMLM A
  labelEl x y sz s (oneRun u)  = textElement "text" (labelAttrs x y sz s) (padText u)
  labelEl x y sz s blank       = textElement "text" (labelAttrs x y sz s) " "
  labelEl x y sz s (oneRow l)  = element "text" (labelAttrs x y sz s) (tspans sz l)
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
