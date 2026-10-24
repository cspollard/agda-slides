{-# OPTIONS --without-K --guardedness #-}

-- Executable: render `Slides.Examples.Intro.demo` to `out/intro/`.
-- Build and run with `make example`.

module Slides.Examples.IntroMain where

open import IO using (Main; run)

open import Slides.Backend.Reveal using (defaultConfig)
open import Slides.Driver
open import Slides.Examples.Intro using (demo)

main : Main
main = run (writeRevealDeck "out/intro" defaultConfig demo)
