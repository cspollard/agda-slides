{-# OPTIONS --without-K --guardedness #-}

-- TextDemo on reveal.js, to `out/text/` (`make text`).

module Slides.Examples.TextDemoMain where

open import IO using (Main; run)

open import Slides.Backend.Reveal using (defaultConfig)
open import Slides.Driver
open import Slides.Examples.TextDemo using (demo)

main : Main
main = run (writeRevealDeck "out/text" defaultConfig demo)
