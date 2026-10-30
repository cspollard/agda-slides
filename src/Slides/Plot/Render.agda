{-# OPTIONS --safe --without-K #-}

-- A plot as a diagram: the lowering `Plot → Dia ℕ`.  Everything printable is already a `Dia`, so
-- every backend, the layout laws and the animations apply to a plot unchanged.
--
--   +-----------------------------------------+   the whole frame is `width × height`
--   | ylabel                                  |   (`layers`: the size of a plot never depends on
--   |  y ┤ ╌╌╌╌╌╌╌╌╌╌╌╌╌╌ grid ╌╌╌╌╌╌╌╌╌╌╌   |   its data)
--   |    ┤        marks (drawn in order)      |
--   |    └───┬───────┬───────┬───────┬──────  |   axes along the left and bottom edges,
--   |       tick labels            xlabel     |   ticks and labels outside the plot box
--   +-----------------------------------------+
--
-- Data are mapped by two axes (`Slides.Plot.Axis`: ℚ to whole pixels, y flipped), so a value
-- outside the range is drawn on the box edge (lines are clipped there instead).  Marks that are lists of points (lines, polygons) are
-- `Polyline`s, scalar-parametric and so animatable; dots and error bars are one `Path` each.
-- Looks come from CSS classes: `plot-axis`, `plot-grid`, `plot-text`, `plot-s1` … (a series colour).

module Slides.Plot.Render where

open import Data.List using (List; []; _∷_; _++_; map; reverse; foldr; concatMap)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _∸_; _/_; _*_; _⊔_)
open import Data.Nat.Show using (show)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ)
open import Data.String using (String) renaming (_++_ to _++ˢ_)

open import Slides.Diagram.Convenience
open import Slides.Diagram.TextMetrics using (textWidth)
open import Slides.Plot.Axis.Rat using (Axis; axisOf; px; flipY)
open import Slides.Plot.Clip using (clipLine)
open import Slides.Plot.Format using (trimmed)
open import Slides.Diagram.Style using (Style)
open import Slides.Plot.Mark
open import Slides.Plot.Ticks.Rat using (ticks)

-- the data range shown on an axis, with its label
record AxisSpec : Set where
  constructor axisSpec
  field
    lo hi : ℚ
    label : String

record Plot : Set where
  constructor plot
  field
    width height : ℕ
    xaxis yaxis  : AxisSpec
    content      : List Series

private
  -- the plot box inside the frame: room at the left for y tick labels, below for x tick labels
  mL mT mR mB fontSize : ℕ
  mL = 64
  mT = 40
  mR = 20
  mB = 72
  fontSize = 20

  record Geo : Set where
    field
      W H bw bh : ℕ      -- the frame and the box
      ax ay     : Axis
      xlo xhi ylo yhi : ℚ
      xlabel ylabel : String

  geo : Plot → Geo
  geo p = record
    { W = W ; H = H ; bw = bw ; bh = bh
    ; ax = axisOf (AxisSpec.lo (Plot.xaxis p)) (AxisSpec.hi (Plot.xaxis p)) bw
    ; ay = axisOf (AxisSpec.lo (Plot.yaxis p)) (AxisSpec.hi (Plot.yaxis p)) bh
    ; xlo = AxisSpec.lo (Plot.xaxis p) ; xhi = AxisSpec.hi (Plot.xaxis p)
    ; ylo = AxisSpec.lo (Plot.yaxis p) ; yhi = AxisSpec.hi (Plot.yaxis p)
    ; xlabel = AxisSpec.label (Plot.xaxis p) ; ylabel = AxisSpec.label (Plot.yaxis p) }
    where W = Plot.width p ; H = Plot.height p
          bw = W ∸ mL ∸ mR ; bh = H ∸ mT ∸ mB

  -- the style with a class for the kind of mark (what CSS paints: a line is stroked and open, a
  -- region filled, a dot filled)
  kind : String → Style → Style
  kind k s = record s { cls = just (maybe′ k (λ c → c ++ˢ " " ++ˢ k) (Style.cls s)) }
    where maybe′ : ∀ {A B : Set} → B → (A → B) → Maybe A → B
          maybe′ d f nothing  = d
          maybe′ d f (just a) = f a

  -- SVG path data
  mv ln : ℕ × ℕ → String
  mv (x , y) = "M" ++ˢ show x ++ˢ " " ++ˢ show y ++ˢ " "
  ln (x , y) = "L" ++ˢ show x ++ˢ " " ++ˢ show y ++ˢ " "

  seg : (ℕ × ℕ) → (ℕ × ℕ) → String
  seg a b = mv a ++ˢ ln b

  cat : List String → String
  cat = foldr _++ˢ_ ""

  -- a filled dot of radius r, as two arcs
  dot : ℕ → ℕ × ℕ → String
  dot r (x , y) = mv (x ∸ r , y) ++ˢ "a" ++ˢ show r ++ˢ " " ++ˢ show r ++ˢ " 0 1 0 " ++ˢ show (2 * r)
                  ++ˢ " 0 a" ++ˢ show r ++ˢ " " ++ˢ show r ++ˢ " 0 1 0 -" ++ˢ show (2 * r) ++ˢ " 0 "

  -- bars of height ± e with caps of half-width c
  bar : ℕ → ℕ × ℕ × ℕ → String
  bar c (x , y₁ , y₂) = seg (x , y₁) (x , y₂) ++ˢ seg (x ∸ c , y₁) (x + c , y₁) ++ˢ seg (x ∸ c , y₂) (x + c , y₂)

  -- a histogram outline: the floor, up to the first height, across, and so on, back to the floor
  outline : ℚ → List ℚ → List ℚ → List (ℚ × ℚ)
  outline floorY []        _  = []
  outline floorY (e ∷ es) hs = (e , floorY) ∷ go e es hs
    where
      go : ℚ → List ℚ → List ℚ → List (ℚ × ℚ)
      go e₀ (e₁ ∷ es′) (h ∷ hs′) = (e₀ , h) ∷ (e₁ , h) ∷ go e₁ es′ hs′
      go e₀ _ _                  = (e₀ , floorY) ∷ []

  module _ (g : Geo) where
    open Geo g

    -- data to frame coordinates
    X Y : ℚ → ℕ
    X x = mL + px ax x
    Y y = mT + flipY ay y

    pt : ℚ × ℚ → ℕ × ℕ
    pt (x , y) = X x , Y y

    put : ℕ → ℕ → Dia ℕ → Dia ℕ
    put = place W H

    inFrame : Dia ℕ → Dia ℕ
    inFrame = put 0 0

    pathOf : String → Style → Dia ℕ
    pathOf d s = inFrame (path W H d s)

    renderMark : Mark → Dia ℕ
    renderMark (line s ps)      = layers W H (map (λ qs → inFrame (polyline (map pt qs) (kind "plot-line" s))) (clipLine xlo xhi ylo yhi ps))
    renderMark (scatter s ps)   = pathOf (cat (map (λ p → dot 3 (pt p)) ps)) (kind "plot-dot" s)
    renderMark (steps s es hs)  = inFrame (polygon (map pt (outline ylo es hs)) (kind "plot-fill" s))
    renderMark (band s ts)      = inFrame (polygon (map (λ { (x , _ , u) → pt (x , u) }) ts ++ map (λ { (x , l , _) → pt (x , l) }) (reverse ts)) (kind "plot-fill" s))
    renderMark (errors s ts)    = pathOf (cat (map (λ { (x , y , e) → bar 3 (X x , Y (y ℚ.- e) , Y (y ℚ.+ e)) }) ts)) (kind "plot-line" s)
      where open import Data.Rational as ℚ using ()
    renderMark (hline s y)      = inFrame (polyline ((mL , Y y) ∷ (mL + bw , Y y) ∷ []) (kind "plot-line" s))
    renderMark (vline s x)      = inFrame (polyline ((X x , mT) ∷ (X x , mT + bh) ∷ []) (kind "plot-line" s))
    renderMark (note x y t)     = put (X x ∸ textWidth fontSize t / 2) (Y y ∸ lineH / 2) (text fontSize t (cls "plot-text"))
      where lineH = fontSize * 3 / 2

    label : String → Dia ℕ
    label t = text fontSize t (cls "plot-text")

    -- grid, axes, tick marks and their labels, from the axis ticks
    xs ys : List ℚ
    xs = ticks 6 (Axis.lo ax) (Axis.hi ax)
    ys = ticks 5 (Axis.lo ay) (Axis.hi ay)

    lineH : ℕ
    lineH = fontSize * 3 / 2

    grid axes : Style → Dia ℕ
    grid s = pathOf (cat (map (λ x → seg (X x , mT) (X x , mT + bh)) xs ++ map (λ y → seg (mL , Y y) (mL + bw , Y y)) ys)) s
    axes s = inFrame (polyline ((mL , mT) ∷ (mL , mT + bh) ∷ (mL + bw , mT + bh) ∷ []) s)
           ⊙ pathOf (cat (map (λ x → seg (X x , mT + bh) (X x , mT + bh + 5)) xs ++ map (λ y → seg (mL ∸ 5 , Y y) (mL , Y y)) ys)) s

    tickLabels : List (Dia ℕ)
    tickLabels = map (λ x → let t = trimmed 3 x in put (X x ∸ textWidth fontSize t / 2) (mT + bh + 8) (label t)) xs
              ++ map (λ y → let t = trimmed 3 y in put (mL ∸ 8 ∸ textWidth fontSize t) (Y y ∸ lineH / 2) (label t)) ys

    titles : List (Dia ℕ)
    titles = put (mL + bw / 2 ∸ textWidth fontSize xlabel / 2) (H ∸ lineH) (label xlabel)
           ∷ put 4 2 (label ylabel) ∷ []

    -- a legend entry: a sample of the mark's style, then its name
    sample : Mark → Maybe (Dia ℕ)
    sample (line s _)     = just (polyline ((0 , 6) ∷ (20 , 6) ∷ []) (kind "plot-line" s))
    sample (scatter s _)  = just (path 20 12 (dot 3 (10 , 6)) (kind "plot-dot" s))
    sample (steps s _ _)  = just (rectangle 20 12 (kind "plot-fill" s))
    sample (band s _)     = just (rectangle 20 12 (kind "plot-fill" s))
    sample (errors s _)   = just (path 20 12 (bar 3 (10 , 0 , 12)) (kind "plot-line" s))
    sample (hline s _)    = just (polyline ((0 , 6) ∷ (20 , 6) ∷ []) (kind "plot-line" s))
    sample (vline s _)    = just (polyline ((0 , 6) ∷ (20 , 6) ∷ []) (kind "plot-line" s))
    sample (note _ _ _)   = nothing

    -- the named entries, as (name, sample)
    entries : List Series → List (String × Dia ℕ)
    entries []                        = []
    entries (series m (just n) ∷ ss) with sample m
    ... | just d  = (n , d) ∷ entries ss
    ... | nothing = entries ss
    entries (series _ nothing ∷ ss)   = entries ss

    entryDia : String × Dia ℕ → Dia ℕ
    entryDia (n , d) = hcat 8 (d ∷ label n ∷ [])

    -- the legend, at the top right of the box
    legend : List Series → Dia ℕ
    legend ss = put (mL + bw ∸ legendW ∸ 12) (mT + 8) (vcatA left 4 (map entryDia es))
      where es = entries ss
            legendW = foldr (λ e w → (28 + textWidth fontSize (proj₁ e)) ⊔ w) 0 es

    -- everything, the top layer first: legend, titles, tick labels, axes, marks (the last on top), grid
    layersOf : List Series → List (Dia ℕ)
    layersOf ss = legend ss
                ∷ titles ++ tickLabels ++ axes (cls "plot-axis")
                ∷ map (λ x → renderMark (Series.mark x)) (reverse ss) ++ grid (cls "plot-grid") ∷ []

drawings : Plot → List (Dia ℕ)
drawings p = layersOf (geo p) (Plot.content p)

render : Plot → Dia ℕ
render p = layers (Plot.width p) (Plot.height p) (drawings p)

-- the style of the n-th series (a CSS class `plot-s1` … colours it)
colour : ℕ → Style
colour n = cls ("plot-s" ++ˢ show n)
