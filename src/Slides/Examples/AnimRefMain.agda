{-# OPTIONS --without-K --guardedness #-}

-- Executable: render `Slides.Examples.AnimRef.deck` as standalone HTML to
-- `out/animref/`.  Build and run with `make animref`.

module Slides.Examples.AnimRefMain where

open import IO using (Main; run)

open import Slides.Backend.Plain using (defaultConfig)
open import Slides.Driver
open import Slides.Examples.AnimRef using (deck)

main : Main
main = run (writePlainDeck "out/animref" defaultConfig deck)
