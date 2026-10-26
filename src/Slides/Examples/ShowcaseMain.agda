{-# OPTIONS --without-K --guardedness #-}

-- Executable: render `Slides.Examples.Showcase.showcase` with both backends,
-- to `out/showcase/` (reveal.js) and `out/showcase-plain/` (standalone HTML),
-- the same deck lowered without notes and diagrams to `out/showcase-lowered/`, and
-- lowered without notes and with animations as stills to `out/showcase-still/`.
-- Build and run with `make showcase`.

module Slides.Examples.ShowcaseMain where

open import Data.Bool using (true)
open import Data.List using (_∷_; [])
open import Data.Maybe using (just)
open import IO using (Main; run; _>>_)

import Slides.Backend.Reveal as Reveal
import Slides.Backend.Plain as Plain
open import Container.Lowering using (_⋙_)
open import Slides.Lower using (lowerDeck; stripNotes; diagramPlaceholder; animationFinal)
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
  ; scripts     = "window.deckLoaded = true;" ∷ []
  }

plainConfig : Plain.PlainConfig
plainConfig = record Plain.defaultConfig { title = "Showcase" }

main : Main
main = run
  ( writeRevealDeck "out/showcase" revealConfig showcase
  >> writePlainDeck "out/showcase-plain" plainConfig showcase
  >> writePlainDeck "out/showcase-lowered" plainConfig
       (lowerDeck (stripNotes ⋙ diagramPlaceholder) showcase)
  >> writePlainDeck "out/showcase-still" plainConfig
       (lowerDeck (stripNotes ⋙ animationFinal) showcase) )
