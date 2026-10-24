{-# OPTIONS --without-K --guardedness #-}

-- Executable: render `Slides.Examples.Showcase.showcase` with both backends,
-- to `out/showcase/` (reveal.js) and `out/showcase-plain/` (standalone HTML).
-- Build and run with `make showcase`.

module Slides.Examples.ShowcaseMain where

open import Data.Bool using (true)
open import Data.Maybe using (just)
open import IO using (Main; run; writeFile; _>>_)

import Slides.Backend.Reveal as Reveal
import Slides.Backend.Plain as Plain
open import Slides.Driver
open import Slides.Examples.Showcase using (showcase)

revealConfig : Reveal.RevealConfig
revealConfig = record Reveal.defaultConfig
  { title       = "Showcase"
  ; theme       = Reveal.whiteTheme
  ; transition  = "fade"
  ; slideNumber = true
  ; width       = just 960
  ; height      = just 700
  }

plainConfig : Plain.PlainConfig
plainConfig = record Plain.defaultConfig { title = "Showcase" }

main : Main
main = run
  ( writeRevealDeck "out/showcase" revealConfig showcase
  >> writePlainDeck "out/showcase-plain" plainConfig showcase )
