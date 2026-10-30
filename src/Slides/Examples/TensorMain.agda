{-# OPTIONS --without-K --guardedness #-}

-- Tensor on reveal.js, to `out/tensor/` (`make tensor`).

module Slides.Examples.TensorMain where

open import IO using (Main; run)

open import Slides.Backend.Reveal using (defaultConfig)
open import Slides.Driver
open import Slides.Examples.Tensor using (demo)

main : Main
main = run (writeRevealDeck "out/tensor" defaultConfig demo)
