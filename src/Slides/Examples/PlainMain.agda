{-# OPTIONS --without-K --guardedness #-}

-- Executable: render `Slides.Examples.Talk.talk` as standalone HTML to
-- `out/plain/`.  Build and run with `make plain`.

module Slides.Examples.PlainMain where

open import IO using (Main; run; writeFile)

open import Slides.Backend.Plain
open import Slides.Examples.Talk using (talk)

main : Main
main = run (writeFile "out/plain/index.html" (renderPlain defaultConfig talk))
