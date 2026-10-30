{-# OPTIONS --without-K --guardedness #-}

-- The deck of `PlotsData`, with the data read from `data/spectrum.csv` (`make plot-data`).

module Slides.Examples.PlotsDataMain where

open import Data.List using (_∷_; [])
open import IO using (Main; run; readFiniteFile; _>>=_)

import Slides.Backend.Reveal as Reveal
open import Slides.Driver
open import Slides.Examples.PlotsData using (talk)

config : Reveal.RevealConfig
config = record Reveal.defaultConfig
  { title = "Plot data"
  ; theme = record Reveal.blackTheme { stylesheets = "slides.css" ∷ "plots.css" ∷ [] } }

main : Main
main = run (readFiniteFile "data/spectrum.csv" >>= λ text → writeRevealDeck "out/plot-data" config (talk text))
