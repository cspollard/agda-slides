{-# OPTIONS --without-K --guardedness #-}

-- Executable: the animations of `Slides.Examples.AnimRef` as a standalone deck, to `out/animref/`,
-- with `refs.json`, the frames Agda computes.  Build and run with `make animref`.

module Slides.Examples.AnimRefMain where

open import IO using (Main; run; writeFile; _>>_)

open import Slides.Backend.Plain using (defaultConfig)
open import Slides.Driver
open import Slides.Examples.AnimRef using (animations; reference)

main : Main
main = run (writePlainDeck "out/animref" defaultConfig animations >> writeFile "out/animref/refs.json" reference)
