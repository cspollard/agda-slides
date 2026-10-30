{-# OPTIONS --without-K --guardedness #-}

-- Talk on reveal.js, to `out/talk/` (`make talk`).

module Slides.Examples.TalkMain where

open import IO using (Main; run)

open import Slides.Backend.Reveal using (defaultConfig)
open import Slides.Driver
open import Slides.Examples.Talk using (talk)

main : Main
main = run (writeRevealDeck "out/talk" defaultConfig talk)
