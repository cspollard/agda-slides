{-# OPTIONS --without-K --guardedness #-}

-- Writing rendered decks to disk.  A deck's `Main` module is a few lines:
--
--   main : Main
--   main = run (writeRevealDeck "out/mytalk" defaultConfig mytalk)
--
-- The directory must exist and hold the assets (the Makefile copies `assets/` and links
-- reveal.js); this only writes the generated files.

module Slides.Driver where

open import Data.String using (String; _++_)
open import IO using (IO; writeFile; _>>_)
open import Level using (0ℓ)
open import Data.Unit.Polymorphic.Base using (⊤)

open import Slides.Deck.Talk using (Talk)
import Slides.Backend.Reveal as Reveal
import Slides.Backend.Plain as Plain

-- reveal.js: `index.html` and `init.js`
writeRevealDeck : String → Reveal.RevealConfig → Talk → IO (⊤ {0ℓ})
writeRevealDeck dir cfg t =
  writeFile (dir ++ "/index.html") (Reveal.renderReveal cfg t)
  >> writeFile (dir ++ "/init.js") (Reveal.initScript t cfg)

-- standalone HTML: `index.html`
writePlainDeck : String → Plain.PlainConfig → Talk → IO (⊤ {0ℓ})
writePlainDeck dir cfg t = writeFile (dir ++ "/index.html") (Plain.renderPlain cfg t)
