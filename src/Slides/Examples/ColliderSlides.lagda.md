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
  ; scanSteps; significance; simDia; gridDia; pairsDia; socksDia; webDia; stages; tilesDia; lhcAnim; triggerAnim )
open import Slides.Examples.TitleAnim using (titleAnim)
open import Slides.Examples.ATLAS using (atlasTurned; atlasBare)

open Checked resources
open Slides.Deck.DSL.Content using () renaming (heading to h■; paragraph to p■; diagram to d■; fragment to f■; classed to c■)

collider : Talk
collider = do
```

**1. Title.**  `Inline` has no line break, so the title is two headings stacked (`h1 + h1` in the css).


```agda
  slide $ do
    heading 1 "how collider physics is"
    heading 1 "accelerating data science"
    classed "subtitle" (p■ "the biggest machine ever built as a data-science lab")
    classed "authors" (p■ "Chris Pollard · Warwick")
    animateLoop "d-title" 85 200 titleAnim

  slide $ do
    heading 2 "curiosity-driven particle physics"
    columns
      ( f■ (d■ "d-higgs" 50 higgsDia)
      ∷ f■ (d■ "d-top" 50 topDia)
      ∷ [] )
    fragment (c■ "center" (p■ "huge (cosmological-scale) implications"))
    fragment (c■ "center" (p■ "only the LHC can produce these particles"))

  slide $
    classed "cover" $ do
      Content.placed 0 0 100 100 $
        Content.figureUnchecked "LHC-FCC.jpg" ""
      c■ "cover-text" $ Content.placed 0 0 100 100 $
        f■ $ p■ "the largest machine(s) ever constructed"

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

  slide $ do
    heading 2 "collaboration → the world wide web"
    diagram "d-web" 100 webDia
    fragment (c■ "callout" (p■ "thousands of physicists, one detector and dataset"))
    fragment (c■ "callout" (p■ ("needed a way to share: the web " ∷ cite "TBL89" ∷ [])))
    fragment (c■ "callout" (p■ "it outgrew its purpose!"))

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

  slide $ do
    heading 2 "a data firehose"
    columns
      ( c■ "callout" (p■ "ATLAS can store about 5000 bunch crossings per second")
      ∷ c■ "callout" (p■ "computers are not fast enough → custom hardware solutions")
      ∷ []
      )
    pause
    columns
      ( c■ "callout" (p■ ("now running sophisticated ML algorithms on FPGAs: very fast ("
          ∷ link "https://fastmachinelearning.org/hls4ml/" ("hls4ml" ∷ [])
          ∷ ", "
          ∷ link "https://fastmachinelearning.org" ("FastML" ∷ [])
          ∷ ")" ∷ []))
      ∷ c■ "callout" (p■ "industry adoption is following")
      ∷ []
      )
    pause
    animateLoop "d-trigger" 100 60 triggerAnim

  slide $ do
    heading 2 "the computing grid"
    diagram "d-grid" 75 gridDia
    fragment (c■ "callout" (p■ "the data are too big to move! send the code to the data..."))
    fragment (c■ "callout" (p■ "170+ computing sites in 40+ countries"))
    fragment (c■ "callout" (p■ "with this much data, one must think carefully about how to summarize events"))

  slide $ do
    heading 2 "statistics with socks"
    diagram "d-socks" 40 socksDia
    incremental
      $ "what fraction of the 🧦 in your drawer are black $f_\\blacksquare$?"
      ∷ "you pull out one sock: black"
      ∷ "you pull out another: blue"
      ∷ "what is your best guess of $f_\\blacksquare$?"
      ∷ "what did you \"store\" in your head to get a number?"
      ∷ "what would you \"store\" in your head if you had a $\\textcolor{#d62839}{\\text{billion}}$ socks?"
      ∷ []

  slide $ do
    heading 2 "estimating a parameter: slide the template"
    animate "d-scan" 90 120 (scan scanSteps 0 ∷ [])
    fragment $ c■ "callout" (p■ "the best choice of $\\mu$ is the one that describes the data best")
    fragment $ c■ "callout" (p■ "how well each $\\mu$ describes the data compared to best determines the uncertainty on $\\mu$")

  slide $ do
    heading 2 "more data, a tighter likelihood"
    animate "d-grow" 75 150 (grow 0 stages ∷ [])
    pause
    classed "callout"
      (p■ "each additional event makes the minimum sharper.")
    pause
    classed "callout"
      (p■ "the width of the curve is the uncertainty: more observations → more certainty")

  slide $ do
    heading 2 "waaaay beyond socks"
    columns
      ( d■ "d-atlas-bare" 100 atlasBare
      ∷ (do f■ (c■ "callout" (p■ "here we are far from counting 🧦"))
            f■ (c■ "callout" (p■ "our detector \"images\" are ~100 million numbers"))
            f■ (c■ "callout" (p■ "how do we find a good event summary that works for billions of events?"))
            f■ (c■ "callout" (p■ "want summaries to simply \"add up\"")))
      ∷ []
      )

  slide $ do
    heading 2 "billions of enormous events"
    diagram "d-pairs" 60 pairsDia
    pause
    paragraph ("this is a widespread problem: inference over many observations of complex data...")
    columns
      ( (f■ $ c■ "callout" (p■ "large-scale medical research"))
      ∷ (f■ $ c■ "callout" (p■ "electoral polling data"))
      ∷ (f■ $ c■ "callout" (p■ "accumulating smart-watch information"))
      ∷ []
      )
    pause
    paragraph ("together with Apple, we derived neural summaries of complex image data that accumulates cleanly up to billions of datapoints " ∷ cite "WKHP26" ∷ [])

  slide $ do
    classed "closing" (p■ "bigger questions → better tools")
    classed "closing" $ Content.incremental
      $ "collider physics poses unique challenges: fast, hard-hitting data"
      ∷ "overcoming these with clever data engineering enables top-notch science..."
      ∷ "...and it's loads of fun"
      ∷ "many of these problems are not unique to collider physics"
      ∷ "percolation to non-scientific activities ongoing"
      ∷ "happy to take questions!"
      ∷ []
    -- TODO
    -- include nice animation from the title slide.

  slide $ do
    heading 2 "references"
    bibliography
```