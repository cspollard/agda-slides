{-# OPTIONS --without-K --guardedness #-}

-- Executable: render `Slides.Examples.Labels.labels` to `out/labels/`.  Build and run with `make labels`.

module Slides.Examples.LabelsMain where

open import IO using (Main; run)

open import Slides.Backend.Reveal using (defaultConfig)
open import Slides.Driver
open import Slides.Examples.Labels using (labels)

main : Main
main = run (writeRevealDeck "out/labels" defaultConfig labels)
