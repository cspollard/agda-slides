{-# OPTIONS --without-K --guardedness #-}

-- A deck with a custom key binding, to `out/keys/` (`make keys`, tested by `make test-keys`).
-- The binding is data: `init.js` gets a `keyboard` option only for keys that differ from reveal.js.

module Slides.Examples.KeysMain where

open import Data.List using (_∷_; [])
open import Data.Maybe using (Maybe)
open import Data.Product using (_,_)
open import IO using (Main; run)

import Slides.Backend.Reveal as Reveal
open import Slides.Backend.Input
open import Slides.Program.Navigation using (next; prev)
open import Slides.Deck.Talk using (Talk; Mode)
open import Slides.Deck.DSL
open import Slides.Driver

-- `q` and right arrow advance, left arrow goes back, the common keys stay; h j k l and up/down are dropped.
binding : Mode → Key → Maybe RCmd
binding _ = decode
  ( (⟨ keyQ ⟩ ∷ ⟨ arrowRight ⟩ ∷ [] , nav next)
  ∷ (⟨ arrowLeft ⟩ ∷ [] , nav prev)
  ∷ commonKinds )

keysDeck : Talk
keysDeck = do
  slide (do heading 2 "Keys"
            paragraph "first"
            pause
            paragraph "second")
  slide (heading 2 "Two")

main : Main
main = run (writeRevealDeck "out/keys" (record Reveal.defaultConfig { binding = binding }) keysDeck)
