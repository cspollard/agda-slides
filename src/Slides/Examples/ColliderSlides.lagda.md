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
  ( fiveSigma; grow; histogram; nllFormula; resources; scan
  ; scanSteps; significance; simDia; stages; tilesDia; lhcAnim )

open Checked resources
open Slides.Deck.DSL.Content using () renaming (heading to h■; paragraph to p■)
```

## The deck

```agda
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
    classed "subtitle" (p■ "how the biggest machine ever built is a data-science lab")
    classed "authors" (p■ "Chris Pollard · Warwick")
```

```agda
  slide $ do
    heading 2 "scientific impact of curiosity-driven particle physics"
    bullets
      ( "Standard Model (SM): mass is granted to particles via their interactions with the Higgs boson."
      ∷ "first demonstrated in the 1960s → took ~50 to experimentally verify!"
      ∷ "finally, an explanation for why radiactive decay is not instant"
      ∷ "top quark has the mass of a gold atom"
      -- TODO: impact on cosmology
      ∷ []
      )
    animateLoop "d-lhc" 100 16 lhcAnim
```

```agda
  slide $ do
    heading 2 "the Large Hadron Collider"
    bullets
      ( "the Large Hadron Collider (LHC) produces 1 billion $pp$ collisions every second at $m_{pp} = 13.6$ TeV"
      ∷ "why?"
      ∷ "rare processes: 1B collisions to get a Higgs boson, on average"
      ∷ ("in 2012 it revealed the " ∷ emph "Higgs boson" ∷ " " ∷ cite "ATLAS12" ∷ " " ∷ cite "CMS12" ∷ [])
      ∷ []
      )
    animateLoop "d-lhc2" 100 16 lhcAnim
```

```agda
  slide $ do
    heading 2 "an early spin-off"
    -- TODO
    -- A nice figure
    bullets
      ( "the LHC collaborations are enormous: ATLAS is ~5000 physicists"
      ∷ "need to coordinate work on detector design, data processing, analysis, etc"
      ∷ "collaborative tools and information-sharing are critical"
      ∷ "the world-wide web (built on the HTTP protocol) was created exactly for this purpose"
      ∷ "clearly they have grown beyond their initial purpose!"
      ∷ []
      )
```

**3. The trigger.**

TODO:
- approximate rates (40MHz -> 100kHz -> 10kHz)
- hardware triggers (ML on FPGAs)
- software triggers (fast ML on GPUs and conventional CPUs)
- hls4ml: https://fastmachinelearning.org/hls4ml/

```agda
  slide $ do
    heading 2 "a data firehose"
    diagram "d-tiles" 100 tilesDia
    classed "callout"
      (p■ "we cannot keep everything, and we cannot look at everything by eye.")
```

**4. computing grid.**

```agda
  slide $ do
    heading 2 "the computing grid"
```

```agda
  slide $ do
    heading 2 "statistical inference"
    columns
      ( (do Content.bullets
              ( "each event is a few thousand numbers: where and when the detector fired"
              ∷ [])
              )
      ∷ (do Content.diagram "d-hist" 100 histogram
            p■ "a signal (red) is a small bump on a smooth background")
      ∷ []
      )
```

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