{-# OPTIONS --without-K --guardedness #-}

-- Executable: render `Slides.Examples.Talk.talk` to `out/talk/`.
-- Build and run with `make talk`.

module Slides.Examples.TalkMain where

open import Data.String using (_++_)
open import IO using (Main; run; writeFile; _>>_)

open import Slides.Backend.Reveal
open import Slides.Examples.Talk using (talk)

main : Main
main = run
  ( writeFile "out/talk/index.html" (renderReveal defaultConfig talk)
  >> writeFile "out/talk/init.js" (initScript defaultConfig) )
