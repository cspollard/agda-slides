# How collider physics is accelerating data science

An outreach talk for undergraduate students, written as a literate Agda file: the prose
here is the commentary, and every `agda` block is checked as part of the deck.  Slides are
built from `Slides.DSL`; the look comes from `assets/collider/collider.css`.  Build and view with
`make collider` (see `docs/Authoring.md` for the vocabulary).

**Before presenting:** the numbers in the deck are round, order-of-magnitude figures.
Check them against the current LHC run and the experiments' public pages, and adjust the
speaker line on the title slide.

```agda
-- TODO
-- unsolved metas
{-# OPTIONS --allow-unsolved-metas --without-K #-}

module Slides.Examples.Collider where

open import Data.Bool using (Bool; false; if_then_else_)
open import Data.List using (List; _∷_; []; zipWith; zip; map; foldr; concat; applyUpTo) renaming (_++_ to _++ˡ_)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _/_; _%_; _⊓_; _≡ᵇ_; _≤ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; length) renaming (_++_ to _++ˢ_)
open import Function using (_$_)

open import Slides.Core using (Deck; emph; strong; codeSpan; inlineMath; link)
open import Slides.DSL
open import Slides.Components using (sectionSlide; resultsTable)
open import Slides.Resources
open import Slides.Diagram
open import Slides.Diagram.Layout
open import Slides.Diagram.Notation hiding (paragraph)
open import Slides.Diagram.Names using (dangling)
open import Slides.Anim.Syntax using (Anim; hold; _⨾_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Slides.Math as M

open Content using () renaming (paragraph to p■; heading to h■)
```

## Resources

Everything the deck may cite.  A citation key that is not listed here is a type error.

```agda
resources : Resources
resources = record
  { figures    = []
  ; references =
      ("ATLAS12" , "ATLAS Collaboration. Observation of a new particle in the search for the Standard Model Higgs boson with the ATLAS detector at the LHC. Phys. Lett. B 716 (2012) 1.")
    ∷ ("CMS12"   , "CMS Collaboration. Observation of a new boson at a mass of 125 GeV with the CMS experiment at the LHC. Phys. Lett. B 716 (2012) 30.")
    ∷ ("CBL20"   , "K. Cranmer, J. Brehmer, G. Louppe. The frontier of simulation-based inference. Proc. Natl. Acad. Sci. (2020). arXiv:1911.01429.")
    ∷ ("WKHP26"  , "A. Wehenkel, M. Kagan, L. Heinrich, C. Pollard. It Just Takes Two: Scaling Amortized Inference to Large Sets. arXiv:2605.07972.")
    ∷ ("TBL89"   , "T. Berners-Lee. Information Management: A Proposal. CERN, 1989.")
    ∷ []
  }

open Checked resources
```

## Diagram vocabulary

Every look comes from a CSS class, so the diagrams restyle with the deck.

```agda
cls : String → Style
cls c = withClass c defaultStyle

dim big : ℕ → String → Dia ℕ
dim  size t = text size t (cls "dim")
big  size t = bold size t (cls "big")

-- a rounded box of a CSS class with a diagram centred on it; the name is for `connect`
card : String → ℕ → ℕ → Dia ℕ → Dia ℕ
card i w h d = named i (framed w h (rounded 18 (withId i (cls "node"))) d)

-- the same box, lit when `on`
stage : Bool → String → ℕ → ℕ → String → List String → Dia ℕ
stage on i w h title body =
  named i (framed w h (rounded 18 (cls (if on then "node on" else "node")))
    (vcat 8 (text 24 title (cls "big") ∷ lines 18 body defaultStyle ∷ [])))
```

## The numbers

Three tiles for the scale of the problem.  A tile is a big number and a caption.

```agda
tile : String → String → List String → Dia ℕ
tile c n body =
  framed 330 190 (rounded 20 (cls "tile"))
    (vcat 14 (bold 44 n (cls c) ∷ lines 19 body defaultStyle ∷ []))

tilesDia : Dia ℕ
tilesDia =
  margin 10 10 10 10
    (hcat 25
      ( tile "stat"         "40 million" ("beam crossings" ∷ "every second" ∷ [])
      ∷ tile "stat crimson" "≈ 1 000"    ("events kept" ∷ "every second" ∷ [])
      ∷ tile "stat plum"    "1 in 10⁹"   ("collisions makes" ∷ "a Higgs boson" ∷ [])
      ∷ []))
```

## From collision to discovery

A pipeline in five stages.  `pipelineDia lit` highlights the stages that satisfy `lit`, and the
slide reveals one more stage at each step (`pipelineActs`).

```agda
pipelineDia : (ℕ → Bool) → Dia ℕ
pipelineDia lit =
  margin 10 20 10 20
    (⟨ stage (lit 1) "s1" 200 150 "collide"  ("protons meet" ∷ "at 13.6 TeV" ∷ [])
     ∷ stage (lit 2) "s2" 200 150 "trigger"  ("keep 1 event" ∷ "in 40 000" ∷ [])
     ∷ stage (lit 3) "s3" 200 150 "store"    ("petabytes on" ∷ "a global grid" ∷ [])
     ∷ stage (lit 4) "s4" 200 150 "learn"    ("machine learning" ∷ "finds patterns" ∷ [])
     ∷ stage (lit 5) "s5" 200 150 "decide"   ("statistics says" ∷ "if it is real" ∷ [])
     ∷ [] ⟩ₕ 50
     ▹[ cls "flow am" ] ("s1" ⟶ "s2" ∷ "s2" ⟶ "s3" ∷ "s3" ⟶ "s4" ∷ "s4" ⟶ "s5" ∷ []))

-- one reveal step lights one more stage; earlier ones stay lit
pipelineActs : List (Anim)
pipelineActs = (hold 1 (pipelineDia (λ _ → false)) ⨾ hold 1 (pipelineDia (_≤ᵇ 1)))
             ∷ hold 1 (pipelineDia (_≤ᵇ 2))
             ∷ hold 1 (pipelineDia (_≤ᵇ 3))
             ∷ hold 1 (pipelineDia (_≤ᵇ 4))
             ∷ hold 1 (pipelineDia (_≤ᵇ 5))
             ∷ []

-- every `connect` names a declared box; a misspelling stops the deck from typechecking
_ : dangling (pipelineDia (λ _ → false)) ≡ []
_ = refl
```

## A bump hunt

A signal is a small excess over a smooth background.  Heights are in diagram units; the
signal bars sit on top of the background bars.

```agda
backgroundBins signalBins : List ℕ
backgroundBins = 60 ∷ 52 ∷ 45 ∷ 39 ∷ 34 ∷ 30 ∷ 26 ∷ 23 ∷ 20 ∷ 18 ∷ 16 ∷ 14 ∷ []
signalBins     =  0 ∷  0 ∷  0 ∷  0 ∷  0 ∷  8 ∷ 20 ∷ 11 ∷  0 ∷  0 ∷  0 ∷  0 ∷ []

histBar : ℕ → ℕ → Dia ℕ
histBar b s =
  ↔ 3 ∥ (rectangle 26 (4 * s) (cls "hist-sig") ═ rectangle 26 (4 * b) (cls "hist-bkg"))

histogram : Dia ℕ
histogram =
  margin 10 10 10 10
    (hcatA bottom 0 (zipWith histBar backgroundBins signalBins) ═ segment 380 0 (cls "axis")
     ═ ↕ 8 ═ dim 18 "mass of the decay products  →")
```

## Mathematics

How sure are we?  The significance of an excess of `s` signal events over `b` background events.

```agda
significance : M.Math
significance = M.rel M.eq (M.var "Z") (M.rel M.approx (M.frac "s" (M.sqrt "b")) "")

-- 5σ
fiveSigma : M.Math
fiveSigma = M.rel M.eq (M.var "Z") (M.juxt 5 (M.greek M.sigma))
```

## Simulation-based inference

A simulator runs forward from parameters to data; inference asks the reverse question.

```agda
simDia : Dia ℕ
simDia =
  margin 10 10 10 10
    ((⟨ card "sp" 300 110 (lines 22 ("parameters θ" ∷ "what we want" ∷ []) defaultStyle)
      ∷ card "ss" 300 110 (lines 22 ("simulator" ∷ "collisions + detector" ∷ []) defaultStyle)
      ∷ card "sx" 300 110 (lines 22 ("data x" ∷ "what we observe" ∷ []) defaultStyle)
      ∷ [] ⟩ₕ 60
      ▹[ cls "flow cy" ] ("sp" ⟶ "ss" ∷ "ss" ⟶ "sx" ∷ []))
     ═ ↕ 14 ═ dim 20 "inference runs the arrow backwards: given x, which θ?")

_ : dangling simDia ≡ []
_ = refl
```

## A likelihood scan

One animation: a gaussian template slides over binned data, and the likelihood of each position
is plotted.  The data are 16 bins of counts with `√(n+1)` error bars.  Everything is whole
numbers: positions are in quarter-bins, the template is a table of `exp(-d²/2σ²)` in thousandths
(σ = 2.2 bins), and the likelihood is the gaussian one, `-2 ln L = Σ (nᵢ - νᵢ)² / σᵢ²` with
`σᵢ² ≈ nᵢ + 1`, times 100 so that it stays an integer.

```agda
counts errs template : List ℕ
counts   = 0 ∷ 0 ∷ 1 ∷ 4 ∷ 10 ∷ 16 ∷ 41 ∷ 36 ∷ 23 ∷ 29 ∷ 23 ∷ 20 ∷ 2 ∷ 3 ∷ 2 ∷ 1 ∷ []
-- five pixels per unit of √(n+1)
errs     = 5 ∷ 5 ∷ 7 ∷ 11 ∷ 17 ∷ 21 ∷ 32 ∷ 30 ∷ 24 ∷ 27 ∷ 24 ∷ 23 ∷ 9 ∷ 10 ∷ 9 ∷ 7 ∷ []
template = 1000 ∷ 994 ∷ 975 ∷ 944 ∷ 902 ∷ 851 ∷ 793 ∷ 729 ∷ 662 ∷ 593 ∷ 524 ∷ 458 ∷ 395 ∷ 336
         ∷ 282 ∷ 234 ∷ 191 ∷ 155 ∷ 123 ∷ 97 ∷ 76 ∷ 58 ∷ 44 ∷ 33 ∷ 24 ∷ 18 ∷ 13 ∷ 9 ∷ 6
         ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ 1 ∷ 1 ∷ []

-- the template at distance d quarter-bins from its centre, in thousandths (0 beyond the table)
tmpl : ℕ → ℕ
tmpl d = go d template
  where go : ℕ → List ℕ → ℕ
        go _       []       = 0
        go zero    (x ∷ _)  = x
        go (suc k) (_ ∷ xs) = go k xs

dist : ℕ → ℕ → ℕ
dist a b = (a ∸ b) + (b ∸ a)

amplitude : ℕ
amplitude = 40

-- expected count in bin i with the template centred at m quarter-bins (the bin centre is 4i+2)
expected : ℕ → ℕ → ℕ
expected m i = amplitude * tmpl (dist (4 * i + 2) m) / 1000

-- -2 ln L at m, times 100, up to a constant
nll : ℕ → ℕ
nll m = foldr _+_ 0
  (zipWith (λ i n → 100 * (dist n (expected m i) * dist n (expected m i)) / suc n)
           (applyUpTo (λ i → i) 16) counts)
```

The scan runs `m = 20 … 44` (μ from 5 to 11), 25 steps.  On the left the template is drawn as
columns of width 5; on the right each step adds one dot.  `base` is the left axis, 230 down.

```agda
scanLo scanSteps : ℕ
scanLo    = 20
scanSteps = 24

-- the smallest -2 ln L over the scan, so the curve can be drawn from its minimum
nllMin : ℕ
nllMin = foldr _⊓_ (nll scanLo) (applyUpTo (λ s → nll (scanLo + s)) (suc scanSteps))

W H : ℕ
W = 800
H = 280

put : ℕ → ℕ → Dia ℕ → Dia ℕ
put x y = place W H x y

canvas : List (Dia ℕ) → Dia ℕ
canvas = foldr (λ d acc → overlay W H acc d) (spacer W H)

-- a data point with its error bar and caps
point : ℕ → ℕ × ℕ → List (Dia ℕ)
point i (n , e) =
    put (36 + 20 * i) (226 ∸ 5 * n) (disc 4 (cls "pt"))
  ∷ put (40 + 20 * i) (230 ∸ 5 * n ∸ e) (segment 0 (2 * e) (cls "eb"))
  ∷ put (35 + 20 * i) (230 ∸ 5 * n ∸ e) (segment 10 0 (cls "eb"))
  ∷ put (35 + 20 * i) (230 ∸ 5 * n + e) (segment 10 0 (cls "eb"))
  ∷ []

dataPoints : List (Dia ℕ)
dataPoints = concat (zipWith point (applyUpTo (λ i → i) 16) (zip counts errs))

-- the template centred at m, as 64 columns
column : ℕ → ℕ → Dia ℕ
column m j = put (28 + 5 * j) (230 ∸ 200 * tmpl (dist j m) / 1000)
                (rectangle 5 (200 * tmpl (dist j m) / 1000) (cls "tmpl"))

-- the dot of step s on the likelihood curve: 315 units of -2 ln L (times 100) per pixel
dot : ℕ → Dia ℕ
dot s = put (427 + 12 * s) (232 ∸ (nll (scanLo + s) ∸ nllMin) / 315) (disc 3 (cls "cur"))

fracStr : ℕ → String
fracStr 0 = "00"
fracStr f = show f

readout : ℕ → String
readout m = "μ = " ++ˢ show (m / 4) ++ˢ "." ++ˢ fracStr ((m % 4) * 25)

-- the axes of both plots and their names (no ticks)
axes : List (Dia ℕ)
axes =
    put 30 20 (segment 0 210 (cls "axis"))
  ∷ put 30 230 (segment 320 0 (cls "axis"))
  ∷ put 430 30 (segment 0 210 (cls "axis"))
  ∷ put 430 240 (segment 300 0 (cls "axis"))
  ∷ put 110 238 (text 18 "observable x (bin)" (cls "dim"))
  ∷ put 520 248 (text 18 "template mean μ" (cls "dim"))
  ∷ put 0 0 (text 18 "counts" (cls "dim"))
  ∷ put 410 0 (text 18 "-2 ln L(μ)" (cls "dim"))
  ∷ []

frame : ℕ → Dia ℕ
frame s = canvas
  ( axes
  ++ˡ dataPoints
  ++ˡ map (column m) (applyUpTo (λ j → j) 64)
  ++ˡ put (30 + 5 * m) 20 (segment 0 210 (cls "mu"))
    ∷ map dot (applyUpTo (λ k → k) (suc s))
  ++ˡ put (424 + 12 * s) (232 ∸ (nll m ∸ nllMin) / 315 ∸ 3) (disc 6 (cls "now"))
    ∷ put 600 20 (text 24 (readout m) (cls "big"))
    ∷ [] )
  where m = scanLo + s

-- one frame per step, played one after the other
scan : ℕ → ℕ → Anim
scan zero    s = hold 1 (frame s)
scan (suc k) s = hold 1 (frame s) ⨾ scan k (suc s)

nllFormula : M.Math
nllFormula = M.raw "-2\\ln L(\\mu) = \\sum_i \\frac{(n_i - \\nu_i(\\mu))^2}{\\sigma_i^2} + \\mathrm{const}"
```

### More data, tighter curve

The second animation adds events over time.  Each stage has its own table of counts (the running
total of twelve batches of simulated events); the template is held at the true mean and its
amplitude grows with the data, and the curve on the right is the likelihood of the data so far.

```agda
-- floor of the square root, by bisection
isqrt : ℕ → ℕ
isqrt n = go 20 0 (suc n)
  where
    go : ℕ → ℕ → ℕ → ℕ
    go zero    lo _  = lo
    go (suc f) lo hi =
      if hi ∸ lo ≤ᵇ 1 then lo
      else (let mid = (lo + hi) / 2 in
            if mid * mid ≤ᵇ n then go f mid hi else go f lo mid)

-- the error bar of a bin with n events: four pixels per unit of √(n+1)
errBar : ℕ → ℕ
errBar n = isqrt (1600 * suc n) / 10

-- as `nll`, for any counts and any template amplitude
nllWith : ℕ → List ℕ → ℕ → ℕ
nllWith amp cs m = foldr _+_ 0
  (zipWith (λ i n → 100 * (dist n (amp * tmpl (dist (4 * i + 2) m) / 1000)
                         * dist n (amp * tmpl (dist (4 * i + 2) m) / 1000)) / suc n)
           (applyUpTo (λ i → i) 16) cs)

-- the batches: counts after 1, 2, … 12 batches of events
stages : List (List ℕ)
stages =
    (0 ∷ 0 ∷ 0 ∷ 3 ∷ 2 ∷ 1 ∷ 2 ∷ 1 ∷ 4 ∷ 3 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷ 1 ∷ 0 ∷ [])
  ∷ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 2 ∷ 1 ∷ 3 ∷ 2 ∷ 8 ∷ 6 ∷ 1 ∷ 3 ∷ 1 ∷ 2 ∷ 1 ∷ 0 ∷ [])
  ∷ (0 ∷ 2 ∷ 2 ∷ 5 ∷ 2 ∷ 3 ∷ 6 ∷ 4 ∷ 13 ∷ 7 ∷ 1 ∷ 3 ∷ 3 ∷ 2 ∷ 2 ∷ 0 ∷ [])
  ∷ (0 ∷ 2 ∷ 3 ∷ 5 ∷ 2 ∷ 4 ∷ 8 ∷ 9 ∷ 16 ∷ 14 ∷ 2 ∷ 6 ∷ 3 ∷ 2 ∷ 2 ∷ 0 ∷ [])
  ∷ (0 ∷ 2 ∷ 3 ∷ 6 ∷ 4 ∷ 6 ∷ 13 ∷ 10 ∷ 21 ∷ 19 ∷ 8 ∷ 6 ∷ 5 ∷ 2 ∷ 2 ∷ 0 ∷ [])
  ∷ (0 ∷ 2 ∷ 3 ∷ 7 ∷ 6 ∷ 7 ∷ 15 ∷ 13 ∷ 23 ∷ 20 ∷ 9 ∷ 6 ∷ 5 ∷ 2 ∷ 2 ∷ 0 ∷ [])
  ∷ (0 ∷ 3 ∷ 3 ∷ 7 ∷ 7 ∷ 9 ∷ 16 ∷ 19 ∷ 25 ∷ 26 ∷ 9 ∷ 6 ∷ 5 ∷ 2 ∷ 2 ∷ 0 ∷ [])
  ∷ (0 ∷ 3 ∷ 3 ∷ 7 ∷ 7 ∷ 14 ∷ 21 ∷ 21 ∷ 30 ∷ 30 ∷ 10 ∷ 7 ∷ 5 ∷ 2 ∷ 2 ∷ 0 ∷ [])
  ∷ (0 ∷ 3 ∷ 3 ∷ 7 ∷ 8 ∷ 16 ∷ 24 ∷ 26 ∷ 37 ∷ 33 ∷ 11 ∷ 9 ∷ 5 ∷ 2 ∷ 3 ∷ 0 ∷ [])
  ∷ (0 ∷ 3 ∷ 3 ∷ 7 ∷ 10 ∷ 18 ∷ 25 ∷ 30 ∷ 42 ∷ 35 ∷ 13 ∷ 10 ∷ 5 ∷ 2 ∷ 3 ∷ 0 ∷ [])
  ∷ (0 ∷ 3 ∷ 4 ∷ 7 ∷ 10 ∷ 21 ∷ 25 ∷ 33 ∷ 47 ∷ 37 ∷ 14 ∷ 11 ∷ 6 ∷ 2 ∷ 3 ∷ 0 ∷ [])
  ∷ (0 ∷ 3 ∷ 4 ∷ 8 ∷ 10 ∷ 22 ∷ 26 ∷ 36 ∷ 51 ∷ 39 ∷ 16 ∷ 12 ∷ 7 ∷ 3 ∷ 3 ∷ 0 ∷ [])
  ∷ []

-- a data point and its error bar at four pixels per count
pointN : ℕ → ℕ → List (Dia ℕ)
pointN i n =
    put (36 + 20 * i) (226 ∸ 4 * n) (disc 4 (cls "pt"))
  ∷ put (40 + 20 * i) (230 ∸ 4 * n ∸ errBar n) (segment 0 (2 * errBar n) (cls "eb"))
  ∷ put (35 + 20 * i) (230 ∸ 4 * n ∸ errBar n) (segment 10 0 (cls "eb"))
  ∷ put (35 + 20 * i) (230 ∸ 4 * n + errBar n) (segment 10 0 (cls "eb"))
  ∷ []

-- the template at the true mean (m = 32), `amp` high at its peak
columnA : ℕ → ℕ → Dia ℕ
columnA amp j = put (28 + 5 * j) (230 ∸ 4 * amp * tmpl (dist j 32) / 1000)
                    (rectangle 5 (4 * amp * tmpl (dist j 32) / 1000) (cls "tmpl"))

-- the likelihood of the counts so far: one dot per position, from its own minimum
curveMin : ℕ → List ℕ → ℕ
curveMin amp cs = foldr _⊓_ (nllWith amp cs scanLo) (applyUpTo (λ k → nllWith amp cs (scanLo + k)) (suc scanSteps))

curveDot : ℕ → List ℕ → ℕ → Dia ℕ
curveDot amp cs k = put (427 + 12 * k) (237 ∸ (nllWith amp cs (scanLo + k) ∸ curveMin amp cs) / 175) (disc 3 (cls "cur"))

-- the picture after batch s (counting from 0), 175 units of -2 ln L (times 100) per pixel
growFrame : ℕ → List ℕ → Dia ℕ
growFrame s cs = canvas
  ( axes
  ++ˡ concat (zipWith pointN (applyUpTo (λ i → i) 16) cs)
  ++ˡ map (columnA amp) (applyUpTo (λ j → j) 64)
  ++ˡ map (curveDot amp cs) (applyUpTo (λ k → k) (suc scanSteps))
  ++ˡ put 560 20 (text 24 ("events: " ++ˢ show (foldr _+_ 0 cs)) (cls "big"))
    ∷ [] )
  where amp = 10 * suc s / 3

-- each batch is shown for three ticks
grow : ℕ → List (List ℕ) → Anim
grow s []             = hold 1 (spacer W H)
grow s (cs ∷ [])      = hold 3 (growFrame s cs)
grow s (cs ∷ rest)    = hold 3 (growFrame s cs) ⨾ grow (suc s) rest

open import Slides.Examples.LHC public using (lhcAnim; lhcFrameAt; lhcTemplate)
```
