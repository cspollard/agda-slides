{-# OPTIONS --without-K --guardedness #-}

-- The plots deck on reveal.js, to `out/plots/` (`make plots`).

module Slides.Examples.PlotsMain where

open import Data.List using (_∷_; [])
open import IO using (Main; run)

import Slides.Backend.Reveal as Reveal
open import Slides.Driver
open import Slides.Examples.Plots using (talk)

config : Reveal.RevealConfig
config = record Reveal.defaultConfig
  { title = "Plots"
  ; theme = record Reveal.blackTheme { stylesheets = "slides.css" ∷ "plots.css" ∷ [] } }

main : Main
main = run (writeRevealDeck "out/plots" config talk)
