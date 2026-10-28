# How collider physics is accelerating data science

An outreach talk for undergraduate students, written as a literate Agda file: the prose
here is the commentary, and every `agda` block is checked as part of the deck.  Slides are
built from `Slides.DSL`; the look comes from `assets/collider/collider.css`.  Build and view with
`make collider` (see `docs/Authoring.md` for the vocabulary).

**Before presenting:** the numbers in the deck are round, order-of-magnitude figures.
Check them against the current LHC run and the experiments' public pages, and adjust the
speaker line on the title slide.

```agda
{-# OPTIONS --safe --without-K #-}

module Slides.Examples.Collider where

open import Data.Bool using (Bool; false; if_then_else_)
open import Data.List using (List; _∷_; []; zipWith)
open import Data.Nat using (ℕ; _≡ᵇ_; _≤ᵇ_; _*_)
open import Data.Product using (_,_)
open import Data.String using (String)

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

## The deck

```agda
collider : Deck
collider = do
```

**1. Title.**

```agda
  slide (do
    classed "tag" (p■ "public lecture for undergraduates")
    heading 1 "how collider physics is accelerating data science"
    classed "subtitle" (p■ "why the biggest experiment ever built is also a data-science laboratory")
    classed "authors" (p■ "Chris Pollard · Warwick")
    notes "welcome. one sentence: particle physicists have been doing big data, machine learning and open science for decades, and the tools they built are now everywhere.")
```

**2. The question.**

```agda
  slide (do
    heading 2 "start with a question"
    incremental
      ( "what is the universe made of, at the smallest scales?"
      ∷ ("how do we find out? " ∷ strong "smash things together." ∷ [])
      ∷ "the Large Hadron Collider (LHC) collides protons 40 million times a second"
      ∷ ("in 2012 it revealed the " ∷ emph "Higgs boson" ∷ " " ∷ cite "ATLAS12" ∷ " " ∷ cite "CMS12" ∷ [])
      ∷ [])
    notes "keep this brisk: the audience should leave the slide knowing the LHC is a data source, not a machine to be explained.")
```

**3. The scale.**

```agda
  slide (do
    heading 2 "a data firehose"
    diagram (compile "d-tiles" 100 tilesDia)
    classed "callout"
      (p■ "we cannot keep everything, and we cannot look at everything by eye.")
    notes "numbers are round and for orientation: 40 MHz crossings, about a kHz written out, and a Higgs boson in roughly one collision in a billion.")
```

**4. The pipeline.**

```agda
  slide (do
    heading 2 "from collision to discovery"
    animate "d-pipeline" 100 400 pipelineActs
    notes "press once per stage. the trigger is a real-time filter made of fast hardware and software; everything after it is offline.")
```

**5. Section: the tools.**

```agda
  sectionSlide "four tools the LHC pushed forward"
```

**6. The tools.**

```agda
  slide (do
    heading 2 "four ideas, now everywhere"
    classed "card blue"
      (do h■ 3 "machine learning"
          p■ "boosted decision trees and neural networks sort signal from background, long before it was fashionable.")
    classed "card crimson"
      (do h■ 3 "simulation & statistics"
          p■ "Monte Carlo simulation and likelihood fits turn raw counts into a calibrated claim.")
    classed "card plum"
      (do h■ 3 "data engineering"
          p■ "real-time triggers, columnar data and a worldwide computing grid.")
    classed "card rust"
      (do h■ 3 "open science"
          p■ ("the web began at CERN " ∷ cite "TBL89" ∷ "; today the data and the software are open." ∷ []))
    notes "each card is a thread of the rest of the talk. ask the audience which they have already met.")
```

**7. Machine learning.**

```agda
  slide (do
    heading 2 "machine learning on every collision"
    columns
      ( (do Content.bullets
              ( "each event is a few thousand numbers: where and when the detector fired"
              ∷ "a network learns which events look like the signal"
              ∷ ("graph neural networks treat particles as " ∷ emph "points that interact" ∷ [])
              ∷ "same ideas: image recognition, fraud detection, medicine"
              ∷ []))
      ∷ (do Content.diagram (compile "d-hist" 100 histogram)
            p■ "a signal (red) is a small bump on a smooth background")
      ∷ [])
    notes "say what a feature is. the histogram is the picture the field has been drawing for fifty years: the bump is the discovery.")
```

**8. Statistics.**

```agda
  slide (do
    heading 2 "when is a bump a discovery?"
    paragraph "a bump this size could come from chance. we ask how often noise alone would fake it."
    displayMath significance
    pause
    paragraph ("particle physics asks for " ∷ inlineMath fiveSigma ∷ ": a fluke about once in 3.5 million tries." ∷ [])
    classed "callout blue"
      (p■ "the same logic checks a medical trial or an A/B test.")
    notes "s over root b is the simple counting limit; real analyses fit a full likelihood, but the intuition survives.")
```

**9. Simulation-based inference.**

```agda
  slide (do
    heading 2 "simulation-based inference"
    diagram (compile "d-sbi" 100 simDia)
    classed "card crimson"
      (do h■ 3 "the physics problem"
          p■ ("we can simulate collisions, but not write down " ∷ inlineMath (M.call "p" (M.rel M.mid "x" (M.greek M.theta) ∷ [])) ∷ []))
    classed "card blue"
      (do h■ 3 "the data-science payoff"
          p■ ("a neural network learns the posterior from simulations alone " ∷ cite "CBL20" ∷ []))
    notes "the forward arrow is easy: run the simulator. the backward arrow is the science. the review (1911.01429) surveys how machine learning turns simulations into inference, in physics and in any field with a simulator: cosmology, epidemiology, climate.")
```

**10. From one event to millions.**

```agda
  slide (do
    heading 2 "one parameter, millions of events"
    paragraph ("a real analysis conditions on a whole " ∷ emph "set" ∷ " of events that share the same θ. training a network on sets that large is too expensive.")
    classed "card plum"
      (do h■ 3 "PAIRS: train on two"
          p■ ("train on sets of at most two events, then finetune on cached summaries. it works for thousands " ∷ cite "WKHP26" ∷ []))
    classed "card rust"
      (do h■ 3 "beyond physics"
          p■ "the same trick applies to images, 3D scenes and molecules: any set of observations that share a hidden cause")
    notes "this is the contribution from the new paper (2605.07972): separate representation learning from posterior modelling. a mean-pooling deep set trained on pairs generalises to any set size; the inference head is then finetuned on pre-aggregated embeddings, so the cost barely depends on the deployment set size. benchmarks: scalar, image, multi-view 3D, molecular and conditional generation, with N in the thousands.")
```

**11. Computing.**

```agda
  slide (resultsTable "built for the LHC, used by everyone"
          ("tool" ∷ "born for" ∷ "now used for" ∷ [])
          (("World Wide Web" ∷ "sharing results between labs" ∷ "everything" ∷ [])
          ∷ ("grid computing" ∷ "analysing LHC data worldwide" ∷ "genomics, climate, astronomy" ∷ [])
          ∷ ("columnar analysis" ∷ "billions of events" ∷ "any large table" ∷ [])
          ∷ ("open data" ∷ "reuse of LHC data" ∷ "reproducible research" ∷ [])
          ∷ []))
```

**12. Try it.**

```agda
  slide (do
    heading 2 "try it yourself"
    paragraph ("real collision data is public: " ∷ link "https://opendata.cern.ch" "opendata.cern.ch" ∷ [])
    code "python" "import uproot, awkward as ak\n\nevents = uproot.open(\"events.root\")[\"Events\"]\npt = events[\"Muon_pt\"].array()\nprint(ak.num(pt).mean(), \"muons per event\")"
    notes "swap in a real open-data file before the talk, and check that the snippet runs.")
```

**13. Closing.**

```agda
  slide (do
    classed "closing" (p■ "big questions make better tools.")
    classed "closing"
      (Content.bullets
        ( "collider physics gave us the web, the grid and much of modern data practice"
        ∷ "its newest ideas are machine learning and open data"
        ∷ ("questions? " ∷ strong "come and ask." ∷ [])
        ∷ []))
    notes "finish on the invitation: summer projects, open data and the department's research groups.")
```

**14. References.**

```agda
  slide (do
    heading 2 "references"
    bibliography)
```
