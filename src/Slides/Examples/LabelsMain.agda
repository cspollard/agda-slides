{-# OPTIONS --without-K --guardedness #-}

-- Executable: render `Slides.Examples.Labels.labels` to `out/labels/` (reveal.js), with
-- `labelMounts` so that `#/intro` etc. address the labelled slides.  `make labels`.

module Slides.Examples.LabelsMain where

open import IO using (Main; run)

open import Container.Lowering using (lower)
open import Slides.Backend.Reveal using (defaultConfig)
open import Slides.Driver
open import Slides.Lower using (labelMounts)
open import Slides.Examples.Labels using (labels)

main : Main
main = run (writeRevealDeck "out/labels" defaultConfig (lower labelMounts labels))
