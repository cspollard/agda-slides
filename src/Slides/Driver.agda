{-# OPTIONS --without-K --guardedness #-}

-- The IO edge: a `Talk` rendered to files.  A deck's `Main` is
--
--   main = run (writeRevealDeck "out/mytalk" defaultConfig mytalk)
--
-- The directory must already hold the assets; only generated files are written.

module Slides.Driver where

open import Data.String using (String; _++_)
open import IO using (IO; writeFile; _>>_)
open import Level using (0ℓ)
open import Data.Unit.Polymorphic.Base using (⊤)

open import Slides.Deck.Talk using (Talk)
import Slides.Backend.Reveal as Reveal
import Slides.Backend.Plain as Plain

writeRevealDeck : String → Reveal.RevealConfig → Talk → IO (⊤ {0ℓ})
writeRevealDeck dir cfg t =
  writeFile (dir ++ "/index.html") (Reveal.renderReveal cfg t)
  >> writeFile (dir ++ "/init.js") (Reveal.initScript t cfg)

writePlainDeck : String → Plain.PlainConfig → Talk → IO (⊤ {0ℓ})
writePlainDeck dir cfg t = writeFile (dir ++ "/index.html") (Plain.renderPlain cfg t)
