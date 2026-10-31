{-# OPTIONS --without-K --guardedness #-}

-- Showcase on both backends (`out/showcase/`, `out/showcase-plain/`) and lowered without notes:
-- diagrams as placeholders (`out/showcase-lowered/`), animations as stills (`out/showcase-still/`).
-- `make showcase`.

module Slides.Examples.ShowcaseMain where

open import Data.List using (_∷_; [])
open import Data.Maybe using (just)
open import IO using (Main; run; _>>_)

import Slides.Backend.Reveal as Reveal
import Slides.Backend.Plain as Plain
open import Slides.Deck.Lower using (lowerTalk; stripNotes; diagramPlaceholder; animationFinal; _⋙ᶠ_)
open import Slides.Driver
open import Slides.Examples.Showcase using (showcase)

revealConfig : Reveal.RevealConfig
revealConfig = record Reveal.defaultConfig
  { title       = "Showcase"
  ; theme       = Reveal.whiteTheme
  ; transition  = "fade"
  ; slideNumber = Data.Bool.true
  ; width       = just 960
  ; height      = just 700
  ; scripts     = "window.deckLoaded = true;" ∷ []
  }
  where import Data.Bool

plainConfig : Plain.PlainConfig
plainConfig = record Plain.defaultConfig { title = "Showcase" }

main : Main
main = run
  ( writeRevealDeck "out/showcase" revealConfig showcase
  >> writePlainDeck "out/showcase-plain" plainConfig showcase
  >> writePlainDeck "out/showcase-lowered" plainConfig
       (lowerTalk (stripNotes ⋙ᶠ diagramPlaceholder) showcase)
  >> writePlainDeck "out/showcase-still" plainConfig
       (lowerTalk (stripNotes ⋙ᶠ animationFinal) showcase) )
