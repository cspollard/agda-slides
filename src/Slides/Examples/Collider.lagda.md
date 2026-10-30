# How collider physics is accelerating data science

An outreach talk for undergraduate students, written as a literate Agda file: the prose
here is the commentary, and every `agda` block is checked as part of the deck.  Slides are
built from `Slides.Deck.DSL`; the look comes from `assets/collider/collider.css`.  Build and view with
`make collider`.  This module holds the figures and animations; `ColliderSlides` is the deck.

**Before presenting:** the numbers in the deck are round, order-of-magnitude figures.
Check them against the current LHC run and the experiments' public pages, and adjust the
speaker line on the title slide.

```agda
{-# OPTIONS --safe --without-K #-}

module Slides.Examples.Collider where

open import Data.Bool using (Bool; false; if_then_else_)
open import Data.List using (List; _∷_; []; zipWith; map; foldr; concat; applyUpTo; reverse)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _/_; _%_; _≡ᵇ_; _≤ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Container.FreeMonad using (pure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Slides.Deck.Literals
open import Slides.Deck.DSL using (Resources; figures; references)
open import Slides.Deck.Anim using (Anim; frame′; hold; ι; _⨾_; liftDia) renaming (_∥_ to _∥ₛ_)
import Slides.Math as M
open import Slides.Diagram.Convenience
open import Slides.Diagram.Style using (filled; stroked; thick)
open import Slides.Diagram.Names using (dangling)
open import Slides.Diagram.TextMetrics using (textWidth)
```

## Resources

Everything the deck may cite.  A citation key that is not listed here is a type error.

```agda
resources : Resources
resources = record
  { figures    = "CMSID.jpg" ∷ "ATLASMS.jpg" ∷ []
  ; references =
      ("ATLAS12" , "ATLAS Collaboration. Observation of a new particle in the search for the Standard Model Higgs boson with the ATLAS detector at the LHC. Phys. Lett. B 716 (2012) 1.")
    ∷ ("CMS12"   , "CMS Collaboration. Observation of a new boson at a mass of 125 GeV with the CMS experiment at the LHC. Phys. Lett. B 716 (2012) 30.")
    ∷ ("CBL20"   , "K. Cranmer, J. Brehmer, G. Louppe. The frontier of simulation-based inference. Proc. Natl. Acad. Sci. (2020). arXiv:1911.01429.")
    ∷ ("WKHP26"  , "A. Wehenkel, M. Kagan, L. Heinrich, C. Pollard. It Just Takes Two: Scaling Amortized Inference to Large Sets. arXiv:2605.07972.")
    ∷ ("TBL89"   , "T. Berners-Lee. Information Management: A Proposal. CERN, 1989.")
    ∷ []
  }
```

(The text of a reference is a `Text`, so it is a string literal at that type: the overloaded
literals of `Slides.Deck.Literals` are imported above.)

## Diagram vocabulary

The deck writes its figures with `Slides.Diagram.Convenience`, all at ℕ, the scalar of a static
figure: `a ∥ b` puts `b` beside `a`, `a ═ b` below, a gap is a spacer (`↔ n`, `↕ n`), `hcat` and
`vcat` join a list with a gap, `margin` pads, `lines` stacks lines of text and `d ▹[ style ] edges`
draws arrows between named boxes.  Every look comes from a CSS class, so the diagrams restyle with
the deck.  (The scene's overlay `∥` is `∥ₛ` here.)

```agda
-- the rounded box of this deck, named for the arrows
box : String → ℕ → ℕ → Dia ℕ → Dia ℕ
box i = card i "node" 18

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

## Two particles

A particle is a big symbol and its name in a rounded square, with what makes it matter written
underneath, one fact to a line.  (A diagram has no TeX: `𝒪(1)` is the unicode letter.)

```agda
particleDia : String → String → String → List String → Dia ℕ
particleDia c sym name facts =
  margin 10 10 10 10
    (vcat 22
      ( framed 240 240 (rounded 24 (cls "tile"))
          (vcat 8 (bold 120 sym (cls c) ∷ text 26 name defaultStyle ∷ []))
      ∷ vcat 8 (map (λ f → text 22 f defaultStyle) facts)
      ∷ []))

higgsDia topDia : Dia ℕ
higgsDia = particleDia "stat" "H" "Higgs boson"
  ("radioactive decay" ∷ "mass of fundamental particles" ∷ "self interaction" ∷ [])
topDia = particleDia "stat crimson" "t" "top quark"
  ("heaviest known particle" ∷ "coupling to Higgs 𝒪(1)" ∷ [])
```

## From collision to discovery

A pipeline in five stages.  `pipelineDia lit` highlights the stages that satisfy `lit`, and the
slide reveals one more stage at each step (`pipelineActs`).

```agda
pipelineDia : (ℕ → Bool) → Dia ℕ
pipelineDia lit =
  margin 10 20 10 20
    (hcat 50
       ( stage (lit 1) "s1" 200 150 "collide"  ("protons meet" ∷ "at 13.6 TeV" ∷ [])
       ∷ stage (lit 2) "s2" 200 150 "trigger"  ("keep 1 event" ∷ "in 40 000" ∷ [])
       ∷ stage (lit 3) "s3" 200 150 "store"    ("petabytes on" ∷ "a global grid" ∷ [])
       ∷ stage (lit 4) "s4" 200 150 "learn"    ("machine learning" ∷ "finds patterns" ∷ [])
       ∷ stage (lit 5) "s5" 200 150 "decide"   ("statistics says" ∷ "if it is real" ∷ [])
       ∷ [] )
     ▹[ cls "flow am" ] ("s1" ⟶ "s2" ∷ "s2" ⟶ "s3" ∷ "s3" ⟶ "s4" ∷ "s4" ⟶ "s5" ∷ []))


-- one reveal step lights one more stage; earlier ones stay lit
pipelineActs : List Anim
pipelineActs = (frame′ 1 (liftDia (pipelineDia (λ _ → false))) ⨾ frame′ 1 (liftDia (pipelineDia (_≤ᵇ 1))))
             ∷ frame′ 1 (liftDia (pipelineDia (_≤ᵇ 2)))
             ∷ frame′ 1 (liftDia (pipelineDia (_≤ᵇ 3)))
             ∷ frame′ 1 (liftDia (pipelineDia (_≤ᵇ 4)))
             ∷ frame′ 1 (liftDia (pipelineDia (_≤ᵇ 5)))
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
significance = M.rel M.eq (M.var "Z") (M.rel M.approx (M.frac (M.var "s") (M.sqrt (M.var "b"))) (M.var ""))

-- 5σ
fiveSigma : M.Math
fiveSigma = M.rel M.eq (M.var "Z") (M.juxt (M.num 5) (M.greek M.sigma))
```

## Simulation-based inference

A simulator runs forward from parameters to data; inference asks the reverse question.

```agda
simDia : Dia ℕ
simDia =
  margin 10 10 10 10
    ((hcat 60
        ( box "sp" 300 110 (lines 22 ("parameters θ" ∷ "what we want" ∷ []) defaultStyle)
        ∷ box "ss" 300 110 (lines 22 ("simulator" ∷ "collisions + detector" ∷ []) defaultStyle)
        ∷ box "sx" 300 110 (lines 22 ("data x" ∷ "what we observe" ∷ []) defaultStyle)
        ∷ [] )
      ▹[ cls "flow cy" ] ("sp" ⟶ "ss" ∷ "ss" ⟶ "sx" ∷ []))
     ═ ↕ 14 ═ dim 20 "inference runs the arrow backwards: given x, which θ?")

_ : dangling simDia ≡ []
_ = refl
```

## The computing grid

An analysis is written once on a laptop; the grid runs it where the data are, and only the small
outputs come back.  Jobs go out in blue, results come back in red.

```agda
gridDia : Dia ℕ
gridDia =
  margin 10 10 10 10
    ((hcat 120
        ( box "gl" 260 110 (lines 22 ("your laptop" ∷ "one analysis" ∷ []) defaultStyle)
        ∷ vcat 20
            ( box "g1" 300 70 (lines 20 ("CERN" ∷ []) defaultStyle)
            ∷ box "g2" 300 70 (lines 20 ("a university cluster" ∷ []) defaultStyle)
            ∷ box "g3" 300 70 (lines 20 ("a national lab" ∷ []) defaultStyle)
            ∷ [] )
        ∷ box "gr" 260 110 (lines 22 ("your laptop" ∷ "merged results" ∷ []) defaultStyle)
        ∷ [] )
      ▹[ cls "flow cy" ] ("gl" ⟶ "g1" ∷ "gl" ⟶ "g2" ∷ "gl" ⟶ "g3" ∷ [])
      ▹[ cls "flow am" ] ("g1" ⟶ "gr" ∷ "g2" ⟶ "gr" ∷ "g3" ⟶ "gr" ∷ []))
     ═ ↕ 14 ═ dim 20 "the code travels to the data; only summaries travel back.")

_ : dangling gridDia ≡ []
_ = refl
```

## Many big events

Eight images stacked like a deck of cards: each is an 8 × 8 grid of noisy cells (a stand-in for
one enormous event), the front one whole and the others showing their top and right edges.  The
colours are pseudo-random, but fixed: a hash of the image and the cell, in whole numbers.

```agda
noiseHue : ℕ → ℕ
noiseHue n = ((n * 7919 + 104729) * (n * 31 + 17) / 7) % 360

-- the colour of cell `c` of image `k`
noiseColour : ℕ → ℕ → String
noiseColour k c = "hsl(" ++ˢ show (noiseHue (k * 64 + c)) ++ˢ ",70%," ++ˢ show (45 + noiseHue (c * 3 + k) % 25) ++ˢ "%)"

cellSide imgSide : ℕ
cellSide = 20
imgSide  = 8 * cellSide

noiseImage : ℕ → Dia ℕ
noiseImage k =
  rectangle imgSide imgSide (stroked "#262626" (thick 2 defaultStyle)) ⊙ grid
  where
    cell : ℕ → Dia ℕ
    cell c = rectangle cellSide cellSide (filled (noiseColour k c) defaultStyle)
    row : ℕ → Dia ℕ
    row r = hcat 0 (map (λ i → cell (r * 8 + i)) (applyUpTo (λ i → i) 8))
    grid : Dia ℕ
    grid = vcat 0 (map row (applyUpTo (λ r → r) 8))

-- image 0 in front at the bottom left, each one further back a step up and to the right
stackStep stackDepth stackSide : ℕ
stackStep  = 14
stackDepth = 7
stackSide  = imgSide + stackDepth * stackStep

stackDia : Dia ℕ
stackDia = layers stackSide stackSide (map layer (applyUpTo (λ k → k) 8))
  where layer : ℕ → Dia ℕ
        layer k = place stackSide stackSide (k * stackStep) ((stackDepth ∸ k) * stackStep) (noiseImage k)
```

## Socks

A sock seen from the side: a leg that bends into an angled foot with a rounded toe, a cuff with
two stripes, and a leaf-shaped heel patch beside the ankle.  The outline and the white heel and toe
patches are curves (`path`, in a 210 × 318 frame); one function draws a sock of any colour.

```agda
sockW sockH : ℕ
sockW = 210
sockH = 318

-- the outline, the white heel and toe patches, and the two cuff stripes (the curves were traced
-- from the sock icon at https://www.svgrepo.com/show/83256/women-socks.svg and smoothed)
sockOutline sockToe sockHeel sockStripes : String
sockOutline = "M176,198 C179,196 188,192 192,188 C197,184 201,179 203,173 C205,168 206,161 206,154 C206,148 204,142 202,136 C200,130 197,124 196,118 C194,112 195,106 194,99 C194,93 194,87 194,80 C194,74 194,68 194,61 C194,55 194,49 194,42 C194,36 194,30 194,24 C194,17 194,8 194,5 L187,0 L102,0 L97,6 C97,9 97,19 97,25 C97,31 97,38 97,44 C97,50 97,57 97,63 C97,69 97,76 97,82 C97,88 97,95 96,101 C96,107 95,114 93,120 C91,126 89,132 86,137 C83,143 79,148 76,153 C72,158 68,163 64,168 C61,173 57,179 53,184 C50,189 46,194 42,199 C38,204 35,209 31,214 C27,219 23,224 20,229 C16,235 12,239 8,245 C6,250 3,256 2,262 C0,268 1,275 2,281 C4,287 7,293 11,298 C15,303 20,307 26,310 C31,312 38,314 44,314 C50,314 57,313 62,310 C68,308 73,304 78,300 C83,296 86,291 91,286 C95,281 99,277 103,272 C108,267 112,262 116,258 C120,253 124,248 128,244 C133,239 137,234 141,229 C145,225 149,220 154,215 C158,211 164,205 168,202 C171,200 175,199 176,198 Z"
sockHeel    = "M185,125 C185,125 187,126 188,127 C189,128 190,131 191,133 C192,135 192,138 193,140 C194,142 194,144 194,146 C195,149 195,151 196,153 C196,155 196,158 196,160 C196,162 195,165 195,167 C194,169 193,171 192,173 C191,175 190,177 188,178 C187,180 185,182 183,183 C181,184 179,185 177,186 C175,187 173,188 171,189 C169,190 166,192 165,192 C164,191 163,188 163,186 C162,184 162,181 162,179 C161,177 161,175 161,172 C161,170 161,168 161,166 C162,163 162,161 162,159 C163,157 164,154 164,152 C165,150 166,148 167,146 C168,144 170,142 171,140 C172,138 173,137 175,135 C176,133 178,131 180,130 C181,128 184,126 185,125 Z"
sockToe     = "M68,296 C67,297 64,299 61,301 C59,302 56,303 53,303 C51,304 48,304 45,304 C42,304 39,304 36,303 C34,302 31,301 29,300 C26,299 24,297 22,295 C20,293 18,291 16,288 C15,286 14,283 13,281 C12,278 11,275 11,272 C11,270 11,267 11,264 C12,261 13,258 14,256 C15,254 18,252 19,251 C20,252 24,253 27,254 C29,256 32,257 34,258 C37,260 39,261 42,263 C44,265 46,266 48,268 C50,270 52,272 54,274 C56,276 58,279 60,281 C61,283 63,286 64,288 C66,290 67,294 68,296 Z"
sockStripes = "M107,10 H184 V23 H107 Z M107,33 H184 V44 H107 Z"

sock : String → Dia ℕ
sock colour =
  layers sockW sockH
    ( path sockW sockH sockStripes (filled "#fff" defaultStyle)
    ∷ path sockW sockH sockHeel (filled "#fff" (stroked "#262626" (thick 4 defaultStyle)))
    ∷ path sockW sockH sockToe (filled "#fff" (stroked "#262626" (thick 4 defaultStyle)))
    ∷ path sockW sockH sockOutline (filled colour (stroked "#262626" (thick 4 defaultStyle)))
    ∷ [] )

socksDia : Dia ℕ
socksDia = margin 10 10 10 10 (hcat 30 (sock "#262626" ∷ sock "#2c5a8a" ∷ sock "#a02a3c" ∷ []))
```

## The PAIRS pipeline

The same stack read as a pipeline: each image is mapped to a one-row image (a summary of one
event), and the summaries are averaged into the one-row summary of the whole dataset.  The
summaries' colours are pseudo-random too; the average of a column is the mean of its eight hues.

```agda
summaryHue : ℕ → ℕ → ℕ
summaryHue k i = noiseHue (1000 + k * 8 + i)

hsl55 : ℕ → String
hsl55 h = "hsl(" ++ˢ show h ++ˢ ",70%,55%)"

-- a one-row image of eight cells
strip : (ℕ → String) → Dia ℕ
strip colour =
  rectangle imgSide cellSide (stroked "#262626" (thick 2 defaultStyle))
    ⊙ hcat 0 (map (λ i → rectangle cellSide cellSide (filled (colour i) defaultStyle)) (applyUpTo (λ i → i) 8))

-- the summary of event `k`, and the mean of the eight summaries
meanStrip : Dia ℕ
meanStrip  = strip (λ i → hsl55 (sumHues i / 8))
  where sumHues : ℕ → ℕ
        sumHues i = foldr _+_ 0 (map (λ k → summaryHue k i) (applyUpTo (λ k → k) 8))

eventStripAt : ℕ → Dia ℕ
eventStripAt k = strip (λ i → hsl55 (summaryHue k i))

-- the eight summaries, one above the other, as tall as the stack
strips : Dia ℕ
strips = vcat ((stackSide ∸ 8 * cellSide) / 7) (map eventStripAt (applyUpTo (λ k → k) 8))

-- a gap with an arrow drawn through it and a caption under the arrow
pairsGap : String → Dia ℕ
pairsGap t = layers 160 stackSide (place 160 stackSide ((160 ∸ textWidth 32 t) / 2) (stackSide / 2 + 14) (dim 32 t) ∷ [])

-- a stage with a caption under it
pairsStage : String → Dia ℕ → String → Dia ℕ
pairsStage i d t = named i d ═ ↕ 12 ═ dim 32 t

pairsDia : Dia ℕ
pairsDia =
  margin 10 10 10 10
    ( hcat 0
        ( pairsStage "pe" stackDia "events"
        ∷ pairsGap "encode"
        ∷ pairsStage "ps" strips "summaries"
        ∷ pairsGap "average"
        ∷ pairsStage "pm" meanStrip "dataset"
        ∷ [] )
    ▹[ cls "flow cy solid" ] ("pe" ⟶ "ps" ∷ "ps" ⟶ "pm" ∷ []) )
```

## The web

Where it came from and where it went: collaborators who needed to share, the web built for them,
and everyone.

```agda
webDia : Dia ℕ
webDia =
  margin 10 10 10 10
    ((hcat 60
        ( box "wp" 300 110 (lines 22 ("collaborators" ∷ "(~5000 on ATLAS)" ∷ []) defaultStyle)
        ∷ box "ww" 300 110 (lines 22 ("the web" ∷ "links + HTTP, 1989" ∷ []) defaultStyle)
        ∷ box "we" 300 110 (lines 22 ("now used everywhere" ∷ []) defaultStyle)
        ∷ [] )
      ▹[ cls "flow cy" ] ("wp" ⟶ "ww" ∷ "ww" ⟶ "we" ∷ []))
     ═ ↕ 14 ═ dim 20 "built to share scientific documentation, now used for everything")

_ : dangling webDia ≡ []
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
one outline of columns of width 5; on the right each step adds one dot.  The baseline of the left plot is 230 down.

```agda
scanLo scanSteps : ℕ
scanLo    = 20
scanSteps = 24

-- the smaller of two numbers by built-in subtraction (`_⊓_` recurses on the value: values here run to millions)
_⊓_ : ℕ → ℕ → ℕ
a ⊓ b = a ∸ (a ∸ b)

-- the smallest -2 ln L over the scan, so the curve can be drawn from its minimum
nllMin : ℕ
nllMin = foldr _⊓_ (nll scanLo) (applyUpTo (λ s → nll (scanLo + s)) (suc scanSteps))

W H : ℕ
W = 800
H = 280

put : ℕ → ℕ → Dia ℕ → Dia ℕ
put = place W H

canvas : List (Dia ℕ) → Dia ℕ
canvas = layers W H

-- A filled shape is one `path`, not a rectangle per column: a template is 64 columns, and the
-- page ships (and draws) one outline of a few hundred bytes instead of 64 boxes.

-- the data points `(y , e)` of the 16 bins (a centre and a half height of the bar): a dot each,
-- and one path of all the error bars with their caps
points : List (ℕ × ℕ) → List (Dia ℕ)
points ys = path W H (foldr _++ˢ_ "" (zipWith bar xs ys)) (cls "eb")
          ∷ zipWith (λ x (y , _) → put (x ∸ 4) (y ∸ 4) (disc 4 (cls "pt"))) xs ys
  where
    xs = applyUpTo (λ i → 40 + 20 * i) 16
    bar : ℕ → ℕ × ℕ → String
    bar x (y , e) = "M" ++ˢ show x ++ˢ " " ++ˢ show (y ∸ e) ++ˢ "V" ++ˢ show (y + e)
                  ++ˢ "M" ++ˢ show (x ∸ 5) ++ˢ " " ++ˢ show (y ∸ e) ++ˢ "h10"
                  ++ˢ "M" ++ˢ show (x ∸ 5) ++ˢ " " ++ˢ show (y + e) ++ˢ "h10"

dataPoints : List (Dia ℕ)
dataPoints = points (zipWith (λ n e → 230 ∸ 5 * n , e) counts errs)

-- the template as an outline, 64 columns 5 wide standing on the baseline (230), of heights `h j` up to `hi`
outline : ℕ → (ℕ → ℕ) → Dia ℕ
outline hi h = put 28 (230 ∸ hi) (path 320 hi ("M0 " ++ˢ show hi ++ˢ stepped 5 (map h (applyUpTo (λ j → j) 64))) (cls "tmpl"))
  where
    stepped : ℕ → List ℕ → String
    stepped x []       = "V" ++ˢ show hi ++ˢ "Z"
    stepped x (c ∷ cs) = "V" ++ˢ show (hi ∸ c) ++ˢ "H" ++ˢ show x ++ˢ stepped (x + 5) cs

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

-- what moves at step s: the template and its mean, the marker and the readout, and under them the
-- curve so far, newest dot first so that frames share their dots (the list is the stack, last on the bottom)
frame : ℕ → Dia ℕ
frame s = canvas
  ( outline 200 (λ j → 200 * tmpl (dist j m) / 1000)
  ∷ put (30 + 5 * m) 20 (segment 0 210 (cls "mu"))
  ∷ put (424 + 12 * s) (232 ∸ (nll m ∸ nllMin) / 315 ∸ 3) (disc 6 (cls "now"))
  ∷ put 600 20 (text 24 (readout m) (cls "big"))
  ∷ map dot (reverse (applyUpTo (λ k → k) (suc s))) )
  where m = scanLo + s

-- the parts that stay: the axes, under everything, and the data, over everything
background foreground : Dia ℕ
background = canvas axes
foreground = canvas dataPoints

-- a leaf present from the start for `d` ticks (a scene with a window)
steady : ℕ → Dia ℕ → Anim
steady d b = hold (ι d) (pure (liftDia b))

-- one frame per step, played one after the other: `suc k` frames from step `s`
steps : ℕ → ℕ → Anim
steps zero    s = frame′ 1 (liftDia (frame s))
steps (suc k) s = frame′ 1 (liftDia (frame s)) ⨾ steps k (suc s)

-- the axes all along, the steps over them, the data over the steps
scan : ℕ → ℕ → Anim
scan k s = steady (suc k) background ∥ₛ steps k s ∥ₛ steady (suc k) foreground

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

-- the likelihood of the counts so far: a curve through one point per position, from its own minimum
curveMin : ℕ → List ℕ → ℕ
curveMin amp cs = foldr _⊓_ (nllWith amp cs scanLo) (applyUpTo (λ k → nllWith amp cs (scanLo + k)) (suc scanSteps))

curve : ℕ → List ℕ → Dia ℕ
curve amp cs = polyline (map pt (applyUpTo (λ k → k) (suc scanSteps))) (cls "curve")
  where
    pt : ℕ → ℕ × ℕ
    pt k = 427 + 12 * k , 237 ∸ (nllWith amp cs (scanLo + k) ∸ curveMin amp cs) / 175

-- the picture after batch s (counting from 0), the data over the template, 175 units of -2 ln L (times 100) per pixel
growFrame : ℕ → List ℕ → Dia ℕ
growFrame s cs = canvas
  ( outline 160 (λ j → 4 * amp * tmpl (dist j 32) / 1000)
  ∷ curve amp cs
  ∷ put 560 20 (text 24 ("events: " ++ˢ show (foldr _+_ 0 cs)) (cls "big"))
  ∷ points (map (λ n → 230 ∸ 4 * n , errBar n) cs) )
  where amp = 10 * suc s / 3

-- each batch is shown for three ticks, over the axes
batches : ℕ → List (List ℕ) → Anim
batches s []             = frame′ 1 (liftDia (spacer W H))
batches s (cs ∷ [])      = frame′ 3 (liftDia (growFrame s cs))
batches s (cs ∷ rest)    = frame′ 3 (liftDia (growFrame s cs)) ⨾ batches (suc s) rest

grow : ℕ → List (List ℕ) → Anim
grow s bs = steady (3 * 12) (canvas axes) ∥ₛ batches s bs
```

The LHC animation is in `Slides.Examples.LHC`.

```agda
open import Slides.Examples.LHC public using (lhcAnim; triggerAnim)
```
