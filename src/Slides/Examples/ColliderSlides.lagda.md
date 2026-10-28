```agda
-- TODO
-- unsolved metas
{-# OPTIONS --allow-unsolved-metas --without-K #-}

module Slides.Examples.ColliderSlides where

open import Data.List using (_∷_; [])
open import Function using (_$_)

import Slides.Math as M
open import Slides.Components using (resultsTable; sectionSlide)
open import Slides.Core using (Deck; emph; inlineMath; link; strong)
open import Slides.Diagram.Layout using (compile)
open import Slides.DSL
open import Slides.Examples.Collider using
  ( fiveSigma; grow; histogram; nllFormula; pipelineActs; resources; scan
  ; scanSteps; significance; simDia; stages; tilesDia; lhcAnim )
open import Slides.Resources as Res

open Res.Checked resources
open Slides.DSL.Content using () renaming (heading to h■; paragraph to p■)
```

## The deck

```agda
collider : Deck
collider = do
```

**1. Title.**  `Inline` has no line break, so the title is two headings stacked (`h1 + h1` in the css).

TODO: add a nice animation of protons colliding at the LHC, particles coalescing
into a set of 8 cubical blocks, representing a data tensor.
The data tensors combine into a single static tensor of the same size that
represnts the full dataset (PAIRS style).
As time goes on, the likelihood curve gets sharper (uncertainty shrinks).

```agda
  slide $ do
    heading 1 "how collider physics is"
    heading 1 "accelerating data science"
    classed "subtitle" (p■ "how the biggest machine ever built is a data-science lab")
    classed "authors" (p■ "Chris Pollard · Warwick")
```

**2. The question.**

```agda
  slide $ do
    heading 2 "the Large Hadron Collider"
    incremental
      ( "the Large Hadron Collider (LHC) produces 1 billion $pp$ collisions every second at $m_{pp} = 13.6$ TeV"
      ∷ "why?"
      ∷ "rare processes: 1B collisions to get a Higgs boson, on average"
      ∷ ("in 2012 it revealed the " ∷ emph "Higgs boson" ∷ " " ∷ cite "ATLAS12" ∷ " " ∷ cite "CMS12" ∷ [])
      ∷ []
      )
    animateLoop "d-lhc" 100 16 lhcAnim
```

**3. The trigger.**

```agda
  slide $ do
    heading 2 "a data firehose"
    diagram (compile "d-tiles" 100 tilesDia)
    classed "callout"
      (p■ "we cannot keep everything, and we cannot look at everything by eye.")
```

**4. The pipeline.**

```agda
  slide $ do
    heading 2 "from collision to discovery"
    animate "d-pipeline" 100 400 pipelineActs
```

**5. Section: the tools.**

```agda
  sectionSlide "four tools the LHC pushed forward"
```

**6. The tools.**

```agda
  slide $ do
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
```

**7. Machine learning.**

```agda
  slide $ do
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
```

**8. Statistics.**

```agda
  slide $ do
    heading 2 "when is a bump a discovery?"
    paragraph "a bump this size could come from chance. we ask how often noise alone would fake it."
    displayMath significance
    pause
    paragraph ("particle physics asks for " ∷ inlineMath fiveSigma ∷ ": a fluke about once in 3.5 million tries." ∷ [])
    classed "callout blue"
      (p■ "the same logic checks a medical trial or an A/B test.")
```

**9. A likelihood scan.**

```agda
  slide $ do
    heading 2 "estimating a likelihood: slide the template"
    animate "d-scan" 75 120 (scan scanSteps 0 ∷ [])
    displayMath nllFormula
    classed "callout blue"
      (p■ "the best-fit mean is where -2 ln L is smallest. near the minimum the curve is a parabola, and its width is the uncertainty.")
```

**10. More data, a tighter curve.**

```agda
  slide $ do
    heading 2 "more data, a tighter likelihood"
    animate "d-grow" 75 150 (grow 0 stages ∷ [])
    classed "callout blue"
      (p■ "each batch of events makes the minimum sharper: the width of the curve is the uncertainty, and it shrinks with the data.")
```

**11. Simulation-based inference.**

```agda
  slide $ do
    heading 2 "simulation-based inference"
    diagram (compile "d-sbi" 100 simDia)
    classed "card crimson"
      (do h■ 3 "the physics problem"
          p■ ("we can simulate collisions, but not write down " ∷ inlineMath (M.call "p" (M.rel M.mid "x" (M.greek M.theta) ∷ [])) ∷ []))
    classed "card blue"
      (do h■ 3 "the data-science payoff"
          p■ ("a neural network learns the posterior from simulations alone " ∷ cite "CBL20" ∷ []))
```

**12. From one event to millions.**

```agda
  slide $ do
    heading 2 "one parameter, millions of events"
    paragraph ("a real analysis conditions on a whole " ∷ emph "set" ∷ " of events that share the same θ. training a network on sets that large is too expensive.")
    classed "card plum"
      (do h■ 3 "PAIRS: train on two"
          p■ ("train on sets of at most two events, then finetune on cached summaries. it works for thousands " ∷ cite "WKHP26" ∷ []))
    classed "card rust"
      (do h■ 3 "beyond physics"
          p■ "the same trick applies to images, 3D scenes and molecules: any set of observations that share a hidden cause")
```

**13. Computing.**

```agda
  slide $ resultsTable "built for the LHC, used by everyone"
          ("tool" ∷ "born for" ∷ "now used for" ∷ [])
          (("World Wide Web" ∷ "sharing results between labs" ∷ "everything" ∷ [])
          ∷ ("grid computing" ∷ "analysing LHC data worldwide" ∷ "genomics, climate, astronomy" ∷ [])
          ∷ ("columnar analysis" ∷ "billions of events" ∷ "any large table" ∷ [])
          ∷ ("open data" ∷ "reuse of LHC data" ∷ "reproducible research" ∷ [])
          ∷ [])
```

**14. Try it.**

```agda
  slide $ do
    heading 2 "try it yourself"
    paragraph ("real collision data is public: " ∷ link "https://opendata.cern.ch" "opendata.cern.ch" ∷ [])
    code "python" "import uproot, awkward as ak\n\nevents = uproot.open(\"events.root\")[\"Events\"]\npt = events[\"Muon_pt\"].array()\nprint(ak.num(pt).mean(), \"muons per event\")"
```

**15. Closing.**

```agda
  slide $ do
    classed "closing" (p■ "big questions make better tools.")
    classed "closing"
      (Content.bullets
        ( "collider physics gave us the web, the grid and much of modern data practice"
        ∷ "its newest ideas are machine learning and open data"
        ∷ ("questions? " ∷ strong "come and ask." ∷ [])
        ∷ []))
```

**16. References.**

```agda
  slide $ do
    heading 2 "references"
    bibliography
```