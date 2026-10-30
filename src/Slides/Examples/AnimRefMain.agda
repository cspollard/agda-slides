{-# OPTIONS --without-K --guardedness #-}

-- AnimRef as a plain deck plus `refs.json`, to `out/animref/` (`make animref`).

module Slides.Examples.AnimRefMain where

open import IO using (Main; run; writeFile; _>>_)

open import Slides.Backend.Plain using (defaultConfig)
open import Slides.Driver
open import Slides.Examples.AnimRef using (animations; reference)

main : Main
main = run (writePlainDeck "out/animref" defaultConfig animations >> writeFile "out/animref/refs.json" reference)
