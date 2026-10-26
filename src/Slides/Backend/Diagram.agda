{-# OPTIONS --safe --without-K #-}

-- HTML rendering of diagrams: inline SVG.
--
-- The shapes are parsnip's `Data.SVG` constructors; `line`, `text` and the
-- arrowhead marker use its `Sanitize` constructors directly.  A diagram is a
-- `<div class="diagram">` holding one `<svg>` with a `viewBox`; the arrowhead
-- marker's `id` is derived from the diagram's name.

module Slides.Backend.Diagram where

open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; _++_; reverse; [_]; map; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _*_; _/_; _%_; suc; _+_; _∸_; _⊔_; _≤ᵇ_; _≟_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; fromList; toList) renaming (_++_ to _++ˢ_)

open import Data.XML.AST using (XMLM)
open import Data.XML.Sanitize using (element; textElement)
import Data.SVG as SVG

open import Slides.Diagram
open import Slides.Core using (Play; onSteps; looping; both)
open import Slides.Diagram.Delta using (Edit; Edits; same; nums; new; grp; done; _∷_; deltas)
open import Data.JSON.AST using (JSON; objectFromList; stringⱼ; numberⱼ; arrayⱼ; jsonNumber; nullⱼ)
open import Data.JSON.Print using (renderJSON)
open import Data.XML.Print using (renderXML)
import Data.Sign as Sign
import Data.Integer as ℤ
import Data.Rational as ℚ
import Slides.Anim.Track as Tr
open import Slides.Diagram.Markup using (Seg; flat; sub; sup; parse)
open import Slides.Backend.HTML using (hElement; padText)
import Slides.Diagram.Draw as Dr
open import Slides.Diagram.Expr using (Expr; ExprOp; eval)
open import Slides.Diagram.Param using (Param; param)
import Slides.Anim.Formula as F
open F using (Formula)
open import Slides.Anim.Phases using (Elem; phasesOf)
open import Slides.Diagram.Scalar using (natOps)
import Slides.Diagram.Place natOps as PN
open import Data.Container.FreeMonad using (pure; impure)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Fin using (zero; suc)
open import Data.Unit using (tt)
import Slides.Diagram.Expr as E
open import Relation.Nullary.Decidable using (⌊_⌋)
import Data.String as Str

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

  -- A label is one `<text>`; markup becomes `<tspan>`s shifted by whole
  -- user units (portable, unlike `baseline-shift`), shrunk for scripts.
  -- `pending` is the shift to undo at the next segment.
  tspans : ℕ → String → List Seg → List (XMLM A)
  tspans sz pending []             = []
  tspans sz pending (flat t ∷ ss)  = textElement "tspan" (opt "dy" (undo pending)) (padText t) ∷ tspans sz "" ss
    where undo : String → Maybe String
          undo "" = nothing
          undo d  = just d
  tspans sz pending (sub t ∷ ss)   =
    textElement "tspan" (("font-size" , num (sz * 7 / 10)) ∷ ("dy" , num (sz / 4)) ∷ []) (padText t)
      ∷ tspans sz ("-" ++ˢ num (sz / 4)) ss
  tspans sz pending (sup t ∷ ss)   =
    textElement "tspan" (("font-size" , num (sz * 7 / 10)) ∷ ("dy" , "-" ++ˢ num (sz / 3)) ∷ []) (padText t)
      ∷ tspans sz (num (sz / 3)) ss

  mutual
    renderElement : String → Element → XMLM A
    renderElement n (rect x y w h s)   =
      SVG.rect (num x) (num y) (num w) (num h) (opt "rx" (Style.rx s ▹′ num) ++ shapeAttrs s)
    renderElement n (circle x y r s)   = SVG.circle (num x) (num y) (num r) (shapeAttrs s)
    renderElement n (line a b c d s)   = lineEl a b c d (shapeAttrs s)
    renderElement n (arrow a b c d s)  =
      lineEl a b c d (shapeAttrs s ++ (("marker-end" , "url(#" ++ˢ markerId n ++ˢ ")") ∷ []))
    renderElement n (label x y sz t s) =
      body (parse t)
      where
        maybeOr : Maybe String → String
        maybeOr nothing  = "currentColor"
        maybeOr (just v) = v
        maybeAnchor : Maybe String → String
        maybeAnchor nothing  = "middle"
        maybeAnchor (just v) = v
        attrs : Attrs
        attrs = ("x" , num x) ∷ ("y" , num y) ∷ ("font-size" , num sz)
              ∷ ("text-anchor" , maybeAnchor (Style.anchor s)) ∷ ("dominant-baseline" , "central")
              ∷ ("fill" , maybeOr (Style.fill s)) ∷ commonAttrs s
        body : List Seg → XMLM A
        body (flat u ∷ []) = textElement "text" attrs (padText u)
        body []            = textElement "text" attrs " "
        body ss            = element "text" attrs (tspans sz "" ss)
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

-- An animation is shipped as its first frame and an edit from each frame to the next
-- (`Slides.Diagram.Delta`, which proves that replaying the edits gives back every
-- frame), in `data-deltas` as JSON, followed by one empty fragment per step.  The
-- page script (`assets/animation.js`) rebuilds the frame it
-- wants from the first one and plays the frames between the resting frames
-- `data-rests`, one every `data-ms` milliseconds.  Without the script the first
-- frame stays.
--
-- An edit is JSON: `0` (unchanged; `-k`, `k` unchanged elements in a row), an array of
-- numbers (the changes of the element's coordinates and sizes, see `numsOf`, from the
-- old values; the rest are unchanged), a string (a replacement element, as an
-- `<svg>` holding it), or `{"g": edits}` (a group edited member by member); a list
-- of edits is an array, ending in `{"r": [strings]}` when elements are appended.
private
  natⱼ : ℕ → JSON
  natⱼ n = numberⱼ (jsonNumber Sign.+ n [] (ℤ.+ 0))

  intⱼ : ℤ.ℤ → JSON
  intⱼ (ℤ.+ n)    = natⱼ n
  intⱼ (ℤ.-[1+ m ]) = numberⱼ (jsonNumber Sign.- (suc m) [] (ℤ.+ 0))

  elementString : String → Element → String
  elementString n e = renderXML (SVG.svg (("xmlns" , "http://www.w3.org/2000/svg") ∷ []) (renderElement n e ∷ []))

  mutual
    editⱼ : String → Edit → JSON
    editⱼ n same      = natⱼ 0
    editⱼ n (nums ns) = arrayⱼ (map intⱼ ns)
    editⱼ n (new e)   = stringⱼ (elementString n e)
    editⱼ n (grp es)  = objectFromList (("g" , editsⱼ n es) ∷ [])

    editsⱼ : String → Edits → JSON
    editsⱼ n es = arrayⱼ (items n es)

    items : String → Edits → List JSON
    items n = go 0
      where
        -- `k` unchanged elements seen so far: a run of two or more is one number `-k`
        flush : ℕ → List JSON → List JSON
        flush 0             r = r
        flush 1             r = natⱼ 0 ∷ r
        flush k@(suc (suc _)) r = numberⱼ (jsonNumber Sign.- k [] (ℤ.+ 0)) ∷ r

        go : ℕ → Edits → List JSON
        go k (done [])   = flush k []
        go k (done rest) = flush k (objectFromList (("r" , arrayⱼ (map (λ e → stringⱼ (elementString n e)) rest)) ∷ []) ∷ [])
        go k (same ∷ es) = go (suc k) es
        go k (e ∷ es)    = flush k (editⱼ n e ∷ go 0 es)

-- the element of an animation, with the attributes that depend on how it is encoded
animationWith : Diagram → List (String × String) → ℕ → Play → XMLM A
animationWith d extra ms play =
  hElement "div"
    ( ("class" , "animation") ∷ ("id" , Diagram.name d ++ˢ "-frames") ∷ ("data-ms" , num ms)
    ∷ extra ++ playAttr play )
    ( hElement "div" (("class" , "frame") ∷ []) (renderDiagram d ∷ [])
    ∷ map (λ _ → hElement "span" (("class" , "fragment anim-step") ∷ []) []) (stepsOf play) )
  where
    commas : List ℕ → String
    commas []       = ""
    commas (n ∷ []) = num n
    commas (n ∷ ns) = num n ++ˢ "," ++ˢ commas ns
    playAttr : Play → List (String × String)
    playAttr (onSteps rs) = ("data-rests" , commas rs) ∷ []
    playAttr looping       = ("data-loop" , "") ∷ []
    playAttr (both rs p)   = ("data-rests" , commas rs) ∷ ("data-loop" , num p) ∷ []
    stepsOf : Play → List ℕ
    stepsOf (onSteps rs) = rs
    stepsOf looping       = []
    stepsOf (both rs p)   = rs

renderAnimation : Diagram → List Diagram → ℕ → Play → XMLM A
renderAnimation d ds ms play =
  animationWith d
    (("data-deltas" , renderJSON (arrayⱼ (map (editsⱼ (Diagram.name d)) (deltas (Diagram.elements d) (map Diagram.elements ds))))) ∷ [])
    ms play

------------------------------------------------------------------------
-- A parametric animation (`Slides.Diagram.Param`) is shipped as a simulator: tracks and formulas.
--
-- `data-param` is JSON `{"v": segments, "p": phases}`, played in real time `τ` (ticks) by the
-- page (`Slides.Anim.Continuous` says what it must draw).  `segments` has, for each segment,
-- `[start tick, pieces]`, with a piece `[ticks, from, to, easing]`: a number is whole and
-- `[n, d]` is the fraction `n/d`; an easing is `0` (Linear), `1` (Step, which jumps at the end
-- of its piece), `2` (StepStart) or `[x₁, y₁, x₂, y₂]` (a cubic Bézier, in hundredths).  A
-- *phase* is a run of ticks whose layouts have the same shape and the same formulas (a segment
-- starting or ending changes it): `{"s": first tick, "b": elements, "c": coordinates}`, with `b`
-- the elements as `<svg>` strings and `c`, for each element, `null` if all its numbers are
-- constants, else its numbers in the order of the player's attribute table, each `null` (a
-- constant) or a formula.  The formulas are evaluated *without rounding* (ℚ, in floating
-- point): a formula is a number, a string `"i"` (the parameter of segment `i`) or an array
-- `[op, a, b]` with `op` one of `"+"`, `"-"` (real subtraction), `"m"` (maximum) and
-- `["%", p, a]` (`p` percent of `a`); `["h", a]` is half of `a` (positions are in half units).
-- Closed subformulas are evaluated here when the result is a non-negative whole number, so
-- only what depends on a parameter (or is not whole) is shipped.  `data-n` is the number of
-- ticks.  The size does not depend on the number of ticks: one phase holds for all of them.
private
  -- a formula as the JSON the player evaluates
  formulaⱼ : Formula → JSON
  formulaⱼ (F.num n)   = natⱼ n
  formulaⱼ (F.var i)   = stringⱼ (num i)
  formulaⱼ (F.add a b) = arrayⱼ (stringⱼ "+" ∷ formulaⱼ a ∷ formulaⱼ b ∷ [])
  formulaⱼ (F.sub a b) = arrayⱼ (stringⱼ "-" ∷ formulaⱼ a ∷ formulaⱼ b ∷ [])
  formulaⱼ (F.max a b) = arrayⱼ (stringⱼ "m" ∷ formulaⱼ a ∷ formulaⱼ b ∷ [])
  formulaⱼ (F.pct p a) = arrayⱼ (stringⱼ "%" ∷ natⱼ p ∷ formulaⱼ a ∷ [])
  formulaⱼ (F.hlf a)   = arrayⱼ (stringⱼ "h" ∷ formulaⱼ a ∷ [])

  coordJ : Maybe Formula → JSON
  coordJ nothing  = nullⱼ
  coordJ (just f) = formulaⱼ f

  -- the numbers of a drawing command: `null` if all are constants, else an entry for each
  -- (`null` for a constant)
  elemCoordsⱼ : Elem → JSON
  elemCoordsⱼ e with Elem.coords e
  ... | nothing = nullⱼ
  ... | just cs = arrayⱼ (map coordJ cs)

  -- the element at the all-zero assignment
  baseElement : Elem → Element
  baseElement e = PN.toElement (Elem.base e)

  phaseFields : String → List Elem → List (String × JSON)
  phaseFields n es =
      ("b" , arrayⱼ (map (λ e → stringⱼ (elementString n (baseElement e))) es))
    ∷ ("c" , arrayⱼ (map elemCoordsⱼ es))
    ∷ []

  -- the phases (`Slides.Anim.Phases.phasesOf`: runs of ticks that ship the same elements)
  phasesⱼ : String → List (Dr.Layout (Expr ℕ)) → List JSON
  phasesⱼ n ls = map (λ p → objectFromList (("s" , natⱼ (proj₁ p)) ∷ phaseFields n (proj₂ p))) (phasesOf ls)

  ratⱼ : ℚ.ℚ → JSON
  ratⱼ q with ℚ.↧ₙ q
  ... | 1 = intⱼ (ℚ.↥ q)
  ... | d = arrayⱼ (intⱼ (ℚ.↥ q) ∷ natⱼ d ∷ [])

  easingⱼ : Tr.Easing → JSON
  easingⱼ Tr.Linear           = natⱼ 0
  easingⱼ Tr.Step             = natⱼ 1
  easingⱼ Tr.StepStart        = natⱼ 2
  easingⱼ (Tr.Bezier a b c d) = arrayⱼ (intⱼ a ∷ intⱼ b ∷ intⱼ c ∷ intⱼ d ∷ [])

  pieceⱼ : Tr.Piece ℚ.ℚ → JSON
  pieceⱼ (Tr.piece n a b e) = arrayⱼ (natⱼ n ∷ ratⱼ a ∷ ratⱼ b ∷ easingⱼ e ∷ [])

  segmentJ : ℕ × List (Tr.Piece ℚ.ℚ) → JSON
  segmentJ (s , ps) = arrayⱼ (natⱼ s ∷ arrayⱼ (map pieceⱼ ps) ∷ [])

renderParamAnimation : Diagram → Param → ℕ → Play → XMLM A
renderParamAnimation d (param ls segs) ms play =
  animationWith d
    ( ("data-n" , num (length ls))
    ∷ ("data-param" , renderJSON (objectFromList
         ( ("v" , arrayⱼ (map segmentJ segs))
         ∷ ("p" , arrayⱼ (phasesⱼ (Diagram.name d) ls))
         ∷ [] )))
    ∷ [] )
    ms play
