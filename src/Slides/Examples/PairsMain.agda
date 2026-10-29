{-# OPTIONS --without-K --guardedness #-}

-- Executable: render `Slides.Examples.Pairs.pairs` with reveal.js to
-- `out/pairs/` (reveal.js from a CDN) or `out/pairs-local/` (a local copy).
-- Build and run with `make pairs` or `make pairs-local REVEAL=…`.

module Slides.Examples.PairsMain where

open import Data.Bool using (true)
open import Data.List using (List; _∷_; [])
open import Data.String using (String)
open import Data.Maybe using (just)
open import IO using (Main; run; IO; _>>=_)
open import Data.Unit.Polymorphic.Base using (⊤)
open import System.Environment using (getArgs)

import Slides.Backend.Reveal as Reveal
open import Slides.Driver
open import Slides.Examples.Pairs using (pairs)

theme : Reveal.Theme
theme = record Reveal.whiteTheme { stylesheets = "slides.css" ∷ "light.css" ∷ "pairs.css" ∷ [] }

config : Reveal.RevealConfig
config = record Reveal.defaultConfig
  { title       = "It Just Takes Two"
  ; theme       = theme
  ; transition  = "slide"
  ; slideNumber = true
  ; width       = just 1280
  ; height      = just 720
  ; scripts     = "Reveal.configure({center: false});" ∷ []
  }

-- `PairsMain cdn` (the default): reveal.js from the jsDelivr CDN, pinned, written
-- to out/pairs/.  `PairsMain local`: a copy of reveal.js linked at
-- out/pairs-local/reveal, written to out/pairs-local/.
build : List String → IO ⊤
build ("local" ∷ _) = writeRevealDeck "out/pairs-local" (Reveal.withSource (Reveal.local "reveal/") config) pairs
build _             = writeRevealDeck "out/pairs"       (Reveal.withSource (Reveal.cdn "6.0.2") config) pairs

main : Main
main = run (getArgs >>= build)
