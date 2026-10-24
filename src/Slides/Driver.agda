{-# OPTIONS --without-K --guardedness #-}

-- Writing rendered decks to disk.  A deck's `Main` module is then a few lines:
--
--   main : Main
--   main = writeRevealDeck "out/mytalk" defaultConfig mytalk
--
-- The directory must exist and contain the assets (`make` targets copy
-- `assets/slides.css` and link reveal.js); this only writes the generated
-- files.

module Slides.Driver where

open import Data.String using (String; _++_)
open import IO using (IO; run; writeFile; _>>_)
open import Level using (0ℓ)
open import Data.Unit.Polymorphic.Base using (⊤)

open import Slides.Core using (Deck)
import Slides.Backend.Reveal as Reveal
import Slides.Backend.Plain as Plain

-- reveal.js: `index.html` and `init.js`.
writeRevealDeck : String → Reveal.RevealConfig → Deck → IO (⊤ {0ℓ})
writeRevealDeck dir cfg d =
  writeFile (dir ++ "/index.html") (Reveal.renderReveal cfg d)
  >> writeFile (dir ++ "/init.js") (Reveal.initScript cfg)

-- standalone HTML: `index.html`.
writePlainDeck : String → Plain.PlainConfig → Deck → IO (⊤ {0ℓ})
writePlainDeck dir cfg d = writeFile (dir ++ "/index.html") (Plain.renderPlain cfg d)
