{-# OPTIONS --safe --without-K #-}

-- Fragments in the elements that hold drawings: a `still`, a `diagram`, an animation.
--
-- The class attributes of the SVG come from the drawings' style strings (`Slides.Diagram.Style.cls`),
-- which `Slides.Diagram.Print` copies into the elements it writes.  `svg? l` is the one condition
-- on them, a check of the layout's inputs and not of the printed output: the class of each draw's
-- style has no `fragment` token as the page sees it (`classSeen`; decidable by computation).
-- Every other attribute of the printed shapes, labels and marker has a fixed name that is not
-- `class`, so given `svg?` the printed `<svg>` holds no fragment (`renderSVG-count`), the wrapper
-- `div`s are counted exactly, and an animation is its `rests`: one `span.fragment.anim-step` per
-- reveal step.
--
--   `renderSVG-count`  a printed layout holds no fragment
--   `still-count`      a still holds the fragments of its SVG
--   `animation-count`  an animation holds the fragments of its first frame, then one per rest

module Slides.Backend.Render.Svg where

open import Data.Bool.Base using (Bool; true; false; T; _∧_; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe.Base using (Maybe; just; nothing)
import Data.Maybe.Base as Maybe
open import Data.Nat.Show using (show)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
import Data.Nat.Properties as ℕP

open import Slides.Backend.HTML using (hElement; hText)
open import Slides.Backend.Animation using (firstFrame; animationEl; stillEl; Play; steps; loop; both; qPrint; animAttrs; animKids; htmlSafe; eventsJSON)
open import Slides.Diagram.Print
open import Slides.Diagram.Style using (Style)
open import Slides.Diagram.Draw using (Layout; Draw; rect; circle; ellipse; poly; line; arrow; label; path)
open import Slides.Text using (TextStyle; style; lines; plainI)
import Data.SVG as SVG
open import Data.XML.Sanitize using (element; textElement)
open import Slides.Backend.Fragments

-- the class of a draw's style has no fragment token
clsOK : Maybe String → Bool
clsOK nothing  = true
clsOK (just c) = classSeen c ≡ᵇ 0

drawStyle : ∀ {S} → Draw S → Style
drawStyle (rect _ _ _ _ s)    = s
drawStyle (circle _ _ _ s)    = s
drawStyle (ellipse _ _ _ _ s) = s
drawStyle (poly _ _ s)        = s
drawStyle (line _ _ _ _ s)    = s
drawStyle (arrow _ _ _ _ s)   = s
drawStyle (label _ _ _ _ s)   = s
drawStyle (path _ _ _ s)      = s

drawsOK : ∀ {S} → List (Draw S) → Bool
drawsOK []       = true
drawsOK (d ∷ ds) = clsOK (Style.cls (drawStyle d)) ∧ drawsOK ds

-- no draw of the layout has a fragment class
svg? : ∀ {S} → Layout S → Bool
svg? l = drawsOK (Layout.draws l)

private
  ∧-split : ∀ {a b} → T (a ∧ b) → T a × T b
  ∧-split {true}  h = tt , h
  ∧-split {false} ()

  -- an element with quiet attributes and no fragments inside has none
  quiet₀ : ∀ tag attrs cs → Quiet attrs → forestCount cs ≡ 0 → fragCount (element tag attrs cs) ≡ 0
  quiet₀ tag attrs cs q h = trans (element-count tag attrs cs) (cong₂ _+_ (quiet-hit attrs q) h)

  quiet-text : ∀ tag attrs t → Quiet attrs → fragCount (textElement tag attrs t) ≡ 0
  quiet-text tag attrs t q = trans (textElement-count tag attrs t) (quiet-hit attrs q)

  leaf₀ : ∀ tag attrs → Quiet attrs → fragCount (element tag attrs []) ≡ 0
  leaf₀ tag attrs q = quiet₀ tag attrs [] q refl

  -- the shapes of `Data.SVG`: a fixed prefix of attributes, then the style's
  rect-count : ∀ x y w h extra → Quiet extra → fragCount (SVG.rect x y w h extra) ≡ 0
  rect-count x y w h extra q = leaf₀ "rect" (("x" , x) ∷ ("y" , y) ∷ ("width" , w) ∷ ("height" , h) ∷ extra) (refl ∷ refl ∷ refl ∷ refl ∷ q)

  circle-count : ∀ cx cy r extra → Quiet extra → fragCount (SVG.circle cx cy r extra) ≡ 0
  circle-count cx cy r extra q = leaf₀ "circle" (("cx" , cx) ∷ ("cy" , cy) ∷ ("r" , r) ∷ extra) (refl ∷ refl ∷ refl ∷ q)

  poly-count : ∀ c pts extra → Quiet extra → fragCount ((if c then SVG.polygon else SVG.polyline) pts extra) ≡ 0
  poly-count true  pts extra q = leaf₀ "polygon" (("points" , pts) ∷ extra) (refl ∷ q)
  poly-count false pts extra q = leaf₀ "polyline" (("points" , pts) ∷ extra) (refl ∷ q)

  path-count : ∀ d extra → Quiet extra → fragCount (SVG.path d extra) ≡ 0
  path-count d extra q = leaf₀ "path" (("d" , d) ∷ extra) (refl ∷ q)

  single : ∀ d → fragCount d ≡ 0 → forestCount (d ∷ []) ≡ 0
  single d h = trans (ℕP.+-identityʳ (fragCount d)) h

  -- attributes of a fixed name other than `class`
  opt-quiet : ∀ k → (∀ v → attrHit ((k , v) ∷ []) ≡ 0) → ∀ m → Quiet (opt k m)
  opt-quiet k h nothing  = []
  opt-quiet k h (just v) = h v ∷ []

  cls-quiet : ∀ m → T (clsOK m) → Quiet (opt "class" m)
  cls-quiet nothing  _ = []
  cls-quiet (just c) h = ℕP.≡ᵇ⇒≡ _ _ h ∷ []

  common-quiet : ∀ s → T (clsOK (Style.cls s)) → Quiet (commonAttrs s)
  common-quiet s h =
    ++⁺ {xs = opt "class" (Style.cls s)} (cls-quiet (Style.cls s) h)
        (++⁺ {xs = opt "id" (Style.ident s)} (opt-quiet "id" (λ _ → refl) _)
             (++⁺ {xs = opt "stroke-dasharray" (Style.dash s)} (opt-quiet "stroke-dasharray" (λ _ → refl) _) (opt-quiet "opacity" (λ _ → refl) _)))

  shape-quiet : ∀ s → T (clsOK (Style.cls s)) → Quiet (shapeAttrs s)
  shape-quiet s h = refl ∷ refl ∷ ++⁺ {xs = opt "stroke-width" (Maybe.map show (Style.strokeWidth s))} (opt-quiet "stroke-width" (λ _ → refl) _) (common-quiet s h)

  style-quiet : ∀ sz st → Quiet (styleAttrs sz st)
  style-quiet sz (style c w z) =
    ++⁺ {xs = opt "fill" c} (opt-quiet "fill" (λ _ → refl) c) (++⁺ {xs = opt "font-weight" w} (opt-quiet "font-weight" (λ _ → refl) w) (opt-quiet "font-size" (λ _ → refl) _))

  mathFont-quiet : ∀ mf → Quiet (mathFontAttrs mf)
  mathFont-quiet noMath = []
  mathFont-quiet mathRm = refl ∷ []
  mathFont-quiet mathIt = refl ∷ refl ∷ []

  rotate-quiet : ∀ x y m → Quiet (rotateAttr x y m)
  rotate-quiet x y nothing  = []
  rotate-quiet x y (just _) = refl ∷ []

  seg-quiet : ∀ sz prev g → Quiet (segAttrs sz prev g)
  seg-quiet sz prev (seg sub   mf st _) =
    refl ∷ ++⁺ {xs = opt "dy" (dyBetween sz prev sub)} (opt-quiet "dy" (λ _ → refl) _)
               (++⁺ {xs = mathFontAttrs mf} (mathFont-quiet mf) (style-quiet sz st))
  seg-quiet sz prev (seg sup   mf st _) =
    refl ∷ ++⁺ {xs = opt "dy" (dyBetween sz prev sup)} (opt-quiet "dy" (λ _ → refl) _)
               (++⁺ {xs = mathFontAttrs mf} (mathFont-quiet mf) (style-quiet sz st))
  seg-quiet sz prev (seg plain mf st _) =
    ++⁺ {xs = opt "dy" (dyBetween sz prev plain)} (opt-quiet "dy" (λ _ → refl) _)
        (++⁺ {xs = mathFontAttrs mf} (mathFont-quiet mf) (style-quiet sz st))

  -- labels: tspans carry only sizes, shifts, fonts and the colours of their styles
  tspanSeg-count : ∀ sz prev g → fragCount (tspanSeg sz prev g) ≡ 0
  tspanSeg-count sz prev g = quiet-text "tspan" (segAttrs sz prev g) (padSpan (Seg.body g)) (seg-quiet sz prev g)

  tspanSegs-count : ∀ sz prev gs → forestCount (tspanSegs sz prev gs) ≡ 0
  tspanSegs-count sz prev []       = refl
  tspanSegs-count sz prev (g ∷ gs) = cong₂ _+_ (tspanSeg-count sz prev g) (tspanSegs-count sz (Seg.scr g) gs)

  tspans-count : ∀ sz is → forestCount (tspans sz is) ≡ 0
  tspans-count sz is = tspanSegs-count sz plain (inlineSegs is)

module _ {S : Set} (P : Print S) where
  private
    lineEl-count : ∀ x₁ y₁ x₂ y₂ extra → Quiet extra → fragCount (lineEl P x₁ y₁ x₂ y₂ extra) ≡ 0
    lineEl-count x₁ y₁ x₂ y₂ extra q = leaf₀ "line" (("x1" , Print.pos P x₁) ∷ ("y1" , Print.pos P y₁) ∷ ("x2" , Print.pos P x₂) ∷ ("y2" , Print.pos P y₂) ∷ extra) (refl ∷ refl ∷ refl ∷ refl ∷ q)

    labelRows-count : ∀ x sz dy ls → forestCount (labelRows P x sz dy ls) ≡ 0
    labelRows-count x sz dy []       = refl
    labelRows-count x sz dy (l ∷ ls) =
      cong₂ _+_ (quiet₀ "tspan" (("x" , Print.pos P x) ∷ ("dy" , dy) ∷ []) (tspans sz l) (refl ∷ refl ∷ []) (tspans-count sz l))
                (labelRows-count x sz _ ls)

    label-quiet : ∀ x y sz st → T (clsOK (Style.cls st)) → Quiet (labelAttrs P x y sz st)
    label-quiet x y sz st h =
      refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl
      ∷ ++⁺ {xs = rotateAttr (Print.pos P x) (Print.pos P y) (Style.rotate st)}
            (rotate-quiet (Print.pos P x) (Print.pos P y) (Style.rotate st))
            (common-quiet st h)

    labelEl-count : ∀ x y sz st → T (clsOK (Style.cls st)) → ∀ L → fragCount (labelEl P x y sz st L) ≡ 0
    labelEl-count x y sz st h (oneRun u)  = quiet-text "text" (labelAttrs P x y sz st) (padText u) (label-quiet x y sz st h)
    labelEl-count x y sz st h blank       = quiet-text "text" (labelAttrs P x y sz st) " " (label-quiet x y sz st h)
    labelEl-count x y sz st h (oneRow l)  = quiet₀ "text" (labelAttrs P x y sz st) (tspans sz l) (label-quiet x y sz st h) (tspans-count sz l)
    labelEl-count x y sz st h (rowsOf ls) =
      quiet₀ "text" (labelAttrs P x y sz st) (labelRows P x sz (firstDy P sz ls) ls) (label-quiet x y sz st h) (labelRows-count x sz _ ls)

    -- the arrowhead has no class
    marker-count : ∀ n → fragCount (marker P n) ≡ 0
    marker-count n =
      quiet₀ "defs" [] (arrowhead P n ∷ []) [] (single (arrowhead P n)
        (quiet₀ "marker" (markerAttrs P n) (SVG.path "M 0 0 L 10 5 L 0 10 z" (("fill" , "currentColor") ∷ []) ∷ [])
                (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ [])
                (single (SVG.path "M 0 0 L 10 5 L 0 10 z" (("fill" , "currentColor") ∷ []))
                        (path-count "M 0 0 L 10 5 L 0 10 z" ((("fill" , "currentColor") ∷ [])) (refl ∷ [])))))

  -- one shape: its attributes are the style's and fixed names
  draw-count : ∀ n (d : Draw S) → T (clsOK (Style.cls (drawStyle d))) → fragCount (renderDraw P n d) ≡ 0
  draw-count n (rect x y w h s) q =
    rect-count (Print.pos P x) (Print.pos P y) (Print.unit P w) (Print.unit P h) (opt "rx" (Maybe.map show (Style.rx s)) ++ shapeAttrs s) (++⁺ {xs = opt "rx" (Maybe.map show (Style.rx s))} (opt-quiet "rx" (λ _ → refl) _) (shape-quiet s q))
  draw-count n (circle x y r s) q = circle-count (Print.pos P x) (Print.pos P y) (Print.unit P r) (shapeAttrs s) (shape-quiet s q)
  draw-count n (ellipse x y a b s) q =
    leaf₀ "ellipse" (("cx" , Print.pos P x) ∷ ("cy" , Print.pos P y) ∷ ("rx" , Print.unit P a) ∷ ("ry" , Print.unit P b) ∷ shapeAttrs s)
          (refl ∷ refl ∷ refl ∷ refl ∷ shape-quiet s q)
  draw-count n (poly c ps s) q = poly-count c (points P ps) (shapeAttrs s) (shape-quiet s q)
  draw-count n (line a b c d s) q  = lineEl-count a b c d (shapeAttrs s) (shape-quiet s q)
  draw-count n (arrow a b c d s) q = lineEl-count a b c d (shapeAttrs s ++ (("marker-end" , "url(#" ++ˢ markerId n ++ˢ ")") ∷ [])) (++⁺ {xs = shapeAttrs s} (shape-quiet s q) (refl ∷ []))
  draw-count n (label x y sz t s) q = labelEl-count x y sz s q (classify (lines t))
  draw-count n (path x y d s) q =
    path-count d (translate (Print.pos P x) (Print.pos P y) ++ shapeAttrs s) (++⁺ {xs = translate (Print.pos P x) (Print.pos P y)} (refl ∷ []) (shape-quiet s q))

  draws-count : ∀ n ds → T (drawsOK ds) → forestCount (map (renderDraw P n) ds) ≡ 0
  draws-count n []       _ = refl
  draws-count n (d ∷ ds) h = cong₂ _+_ (draw-count n d (proj₁ (∧-split h))) (draws-count n ds (proj₂ (∧-split h)))

  -- a printed layout holds no fragment
  renderSVG-count : ∀ n pct l → T (svg? l) → fragCount (renderSVG P n pct l) ≡ 0
  renderSVG-count n pct l h =
    quiet₀ "svg" (("xmlns" , "http://www.w3.org/2000/svg") ∷ svgAttrs P pct l) (marker P n ∷ map (renderDraw P n) (Layout.draws l)) (refl ∷ refl ∷ refl ∷ [])
      (cong₂ _+_ (marker-count n) (draws-count n (Layout.draws l) h))

-- a still: a `div.diagram` around its SVG
still-count : ∀ n pct l → T (svg? l) → fragCount (stillEl n pct l) ≡ 0
still-count n pct l h =
  trans (hElement-count "div" (("class" , "diagram") ∷ ("id" , n) ∷ []) (renderSVG qPrint n pct l ∷ []))
        (cong (λ x → 0 + (x + 0)) (renderSVG-count qPrint n pct l h))

private
  -- no class of the attributes has a fragment
  anim-hit : ∀ name ms play a rs → attrHit (animAttrs name ms play a rs) ≡ 0
  anim-hit name ms steps     a []      = refl
  anim-hit name ms loop      a []      = refl
  anim-hit name ms (both k)  a []      = refl
  anim-hit name ms steps     a (_ ∷ _) = refl
  anim-hit name ms loop      a (_ ∷ _) = refl
  anim-hit name ms (both k)  a (_ ∷ _) = refl

  -- each rest is one fragment
  span-count : ∀ {A : Set} (rs : List A) →
               forestCount (map (λ _ → hElement "span" (("class" , "fragment anim-step") ∷ []) []) rs) ≡ length rs
  span-count []       = refl
  span-count (_ ∷ rs) = cong suc (span-count rs)

  -- the frame, the data and the rests of an animation
  kids-count : ∀ name pct a rs → fragCount (renderSVG qPrint name pct (firstFrame a)) ≡ 0 →
               forestCount (animKids name pct a rs) ≡ length rs
  kids-count name pct a rs h =
    cong₂ _+_ (trans (hElement-count "div" (("class" , "frame") ∷ [])
                        (hElement "div" (("class" , "diagram") ∷ ("id" , name) ∷ []) (renderSVG qPrint name pct (firstFrame a) ∷ []) ∷ []))
                     (cong (λ x → 0 + (x + 0)) diagram-zero))
              (cong₂ _+_ (hText-count "script" (("type" , "application/json") ∷ ("class" , "events") ∷ []) (htmlSafe (eventsJSON a))) (span-count rs))
    where
      diagram-zero : fragCount (hElement "div" (("class" , "diagram") ∷ ("id" , name) ∷ [])
                                  (renderSVG qPrint name pct (firstFrame a) ∷ [])) ≡ 0
      diagram-zero = trans (hElement-count "div" (("class" , "diagram") ∷ ("id" , name) ∷ []) (renderSVG qPrint name pct (firstFrame a) ∷ [])) (cong (λ x → 0 + (x + 0)) h)

  -- an animation: the fragments of its first frame, then one per rest
  animation-count′ : ∀ name pct ms play a rs → fragCount (renderSVG qPrint name pct (firstFrame a)) ≡ 0 →
                     fragCount (animationEl name pct ms play a rs) ≡ length rs
  animation-count′ name pct ms play a rs h =
    trans (hElement-count "div" (animAttrs name ms play a rs) (animKids name pct a rs))
          (cong₂ _+_ (anim-hit name ms play a rs) (kids-count name pct a rs h))

animation-count : ∀ name pct ms play a rs → T (svg? (firstFrame a)) →
                  fragCount (animationEl name pct ms play a rs) ≡ length rs
animation-count name pct ms play a rs h = animation-count′ name pct ms play a rs (renderSVG-count qPrint name pct (firstFrame a) h)
