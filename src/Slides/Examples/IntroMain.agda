{-# OPTIONS --without-K --guardedness #-}

-- Executable: render `Slides.Examples.Intro.demo` to `out/intro/`.
-- Build and run with `make example`.

module Slides.Examples.IntroMain where

open import Data.String using (_++_)
open import IO using (Main; run; writeFile; _>>_)

open import Slides.Backend.Reveal
open import Slides.Examples.Intro using (demo)

main : Main
main = run
  ( writeFile "out/intro/index.html" (renderReveal defaultConfig demo)
  >> writeFile "out/intro/init.js" (initScript defaultConfig) )
