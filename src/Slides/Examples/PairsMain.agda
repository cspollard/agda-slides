{-# OPTIONS --without-K --guardedness #-}

-- Executable: render `Slides.Examples.Pairs.pairs` with reveal.js to
-- `out/pairs/`.  Build and run with `make pairs`.

module Slides.Examples.PairsMain where

open import Data.Bool using (true)
open import Data.List using (_∷_; [])
open import Data.Maybe using (just)
open import IO using (Main; run)

import Slides.Backend.Reveal as Reveal
open import Slides.Driver
open import Slides.Examples.Pairs using (pairs)

theme : Reveal.Theme
theme = record Reveal.blackTheme { stylesheets = "slides.css" ∷ "pairs.css" ∷ [] }

config : Reveal.RevealConfig
config = record Reveal.defaultConfig
  { title       = "It Just Takes Two"
  ; theme       = theme
  ; transition  = "slide"
  ; slideNumber = true
  ; width       = just 1280
  ; height      = just 720
  ; scriptFiles = "pairs.js" ∷ []
  ; scripts     = "Reveal.configure({center: false});" ∷ []
  }

main : Main
main = run (writeRevealDeck "out/pairs" config pairs)
