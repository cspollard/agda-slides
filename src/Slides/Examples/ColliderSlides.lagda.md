# The deck

The slides of the talk, in the order they are given; the figures, animations and the resources
they cite are in `Slides.Examples.Collider`.

```agda
{-# OPTIONS --safe --without-K #-}

module Slides.Examples.ColliderSlides where

open import Data.List using (_∷_; [])
open import Function using (_$_)

import Slides.Deck.Math as M
open import Slides.Deck.Talk using (Talk)
open import Slides.Deck.DSL
open import Slides.Examples.Collider using
  ( higgsDia; topDia; fiveSigma; grow; histogram; nllFormula; resources; scan
  ; scanSteps; significance; simDia; gridDia; webDia; stages; tilesDia; lhcAnim; triggerAnim )
open import Slides.Examples.ATLAS using (atlasTurned)

open Checked resources
open Slides.Deck.DSL.Content using () renaming (heading to h■; paragraph to p■; diagram to d■; fragment to f■; classed to c■)

collider : Talk
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
    classed "subtitle" (p■ "the biggest machine ever built is a data-science lab")
    classed "authors" (p■ "Chris Pollard · Warwick")

  slide $ do
    heading 2 "curiosity-driven particle physics"
    columns
      ( f■ (d■ "d-higgs" 50 higgsDia)
      ∷ f■ (d■ "d-top" 50 topDia)
      ∷ [] )
    fragment (c■ "center" (p■ "huge (cosmological-scale) implications"))
    fragment (c■ "center" (p■ "only the LHC can produce these particles"))

  slide $ do
    heading 2 "collaboration → the world wide web"
    diagram "d-web" 100 webDia
    fragment (c■ "callout" (p■ "thousands of physicists, one dataset"))
    fragment (c■ "callout" (p■ ("so CERN built a way to share: the web " ∷ cite "TBL89" ∷ [])))
    fragment (c■ "callout" (p■ "it outgrew its purpose"))

  slide $ do
    heading 2 "the ATLAS detector"
    diagram "d-atlas" 60 atlasTurned
    columns
      ( f■ (c■ "callout" $ p■ "~100 million readout channels")
      ∷ f■ (c■ "callout" $ p■ "1.5-2 MB per bunch crossing")
      ∷ []
      )

  slide $
    classed "cover" $ Content.placed 0 0 100 100 $
      Content.figureUnchecked "CMSID.jpg" ""

  slide $
    classed "cover" $ Content.placed 0 0 100 100 $
      Content.figureUnchecked "ATLASMS.jpg" ""
```

```agda
  slide $ do
    heading 2 "a data firehose"
    animateLoop "d-lhc" 50 60 lhcAnim
    pause
    columns
      ( c■ "callout" (p■ "LHC bunches cross 40 million times per second")
      ∷ c■ "callout" (p■ "about 65 $pp$ collisions per bunch crossing (→ 200 after upgrade)")
      ∷ []
      )
    pause
    columns
      ( c■ "callout" (p■ "~1 billion collisions per second (!)")
      ∷ c■ "callout" (p■ "→ 100TB/s of data per experiment (!)")
      ∷ []
      )

  slide $
    classed "cover" $ do
      Content.placed 0 0 100 100 $
        Content.figureUnchecked "LHC-FCC.jpg" ""
      c■ "cover-text" $ Content.placed 0 0 100 100 $
        f■ $ p■ "the largest machine(s) ever constructed"
```

TODO: LHC image here

```agda
  slide $ do
    heading 2 "a data firehose"
    columns
      ( c■ "callout" (p■ "ATLAS can store about 5000 bunch crossings per second")
      ∷ c■ "callout" (p■ "computers are not fast enough → custom hardware solutions")
      ∷ []
      )
    pause
    columns
      ( c■ "callout" (p■ "now running sophisticated ML algorithsm on FPGAs: very fast")
      ∷ c■ "callout" (p■ "industry adoption is following")
      ∷ []
      )
    animateLoop "d-trigger" 100 60 triggerAnim
```

**4. computing grid.**

```agda
  slide $ do
    heading 2 "the computing grid"
    diagram "d-grid" 100 gridDia
    fragment (c■ "callout" (p■ "the data are too big to move: send the code to the data"))
    fragment (c■ "callout" (p■ "each site runs your analysis on its own slice"))
    fragment (c■ "callout" (p■ "only small summaries come back to your laptop"))
```

```agda
  slide $ do
    heading 2 "statistical inference"
    columns
      $ (Content.bullets
          $ "each event is a few thousand numbers: where and when the detector fired"
          ∷ [])
      ∷ (do Content.diagram "d-hist" 100 histogram
            p■ "a signal (red) is a small bump on a smooth background")
      ∷ []
```

```agda
  slide $ do
    heading 2 "when is a bump a discovery?"
    paragraph "a bump this size could come from chance. we ask how often noise alone would fake it."
    displayMath significance
    pause
    paragraph ("particle physics asks for " ∷ inlineMath fiveSigma ∷ ": a fluke about once in 3.5 million tries." ∷ [])
    pause
    classed "callout blue"
      (p■ "the same logic checks a medical trial or an A/B test.")
```

TODO: socks example

- you want to estimate the fraction of black socks in your drawer
- you pull out one sock: it is black
- you pull out another sock: it is blue.
- what is your estimate of the fraction of black socks?
- what numbers did you keep in your head to make that calculation possible?

```agda
  slide $ do
    heading 2 "an example with socks"
```

```agda
  slide $ do
    heading 2 "estimating a parameter: slide the template"
    animate "d-scan" 75 120 (scan scanSteps 0 ∷ [])
    displayMath nllFormula
    classed "callout blue"
      (p■ "the best-fit mean is where -2 ln L is smallest. near the minimum the curve is a parabola, and its width is the uncertainty.")
```

```agda
  slide $ do
    heading 2 "more data, a tighter likelihood"
    animate "d-grow" 75 150 (grow 0 stages ∷ [])
    classed "callout blue"
      (p■ "each batch of events makes the minimum sharper: the width of the curve is the uncertainty, and it shrinks with the data.")
```

```agda
  slide $ do
    heading 2 "simulation-based inference"
    diagram "d-sbi" 100 simDia
    classed "card crimson" $ do
      h■ 3 "the physics problem"
      p■ ("we can simulate collisions, but not write down " ∷ inlineMath (M.call "p" (M.rel M.mid "x" (M.greek M.theta) ∷ [])) ∷ [])
    classed "card blue" $ do
      h■ 3 "the data-science payoff"
      p■ ("a neural network learns the posterior from simulations alone " ∷ cite "CBL20" ∷ [])
```

**12. From one event to millions.**

```agda
  slide $ do
    heading 2 "one parameter, millions of events"
    paragraph ("a real analysis conditions on a whole " ∷ emph "set" ∷ " of events that share the same θ. training a network on sets that large is too expensive.")
    classed "card plum" $ do
      h■ 3 "PAIRS: train on two"
      p■ ("train on sets of at most two events, then finetune on cached summaries. it works for thousands " ∷ cite "WKHP26" ∷ [])
    classed "card rust" $ do
      h■ 3 "beyond physics"
      p■ "the same trick applies to images, 3D scenes and molecules: any set of observations that share a hidden cause"
```

**13. Computing.**

```agda
  slide $
    resultsTable "built for the LHC, used by everyone" ("tool" ∷ "born for" ∷ "now used for" ∷ [])
      $ ("World Wide Web" ∷ "sharing results between labs" ∷ "everything" ∷ [])
      ∷ ("grid computing" ∷ "analysing LHC data worldwide" ∷ "genomics, climate, astronomy" ∷ [])
      ∷ ("columnar analysis" ∷ "billions of events" ∷ "any large table" ∷ [])
      ∷ ("open data" ∷ "reuse of LHC data" ∷ "reproducible research" ∷ [])
      ∷ []
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
    classed "closing" $ Content.bullets
      $ "collider physics gave us the web, the grid and much of modern data practice"
      ∷ "its newest ideas are machine learning and open data"
      ∷ ("questions? " ∷ strong "come and ask." ∷ [])
      ∷ []
```

**16. References.**

```agda
  slide $ do
    heading 2 "references"
    bibliography
```