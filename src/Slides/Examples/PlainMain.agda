{-# OPTIONS --without-K --guardedness #-}

-- Talk on the standalone HTML backend, to `out/plain/` (`make plain`).

module Slides.Examples.PlainMain where

open import IO using (Main; run)

open import Slides.Backend.Plain using (defaultConfig)
open import Slides.Driver
open import Slides.Examples.Talk using (talk)

main : Main
main = run (writePlainDeck "out/plain" defaultConfig talk)
