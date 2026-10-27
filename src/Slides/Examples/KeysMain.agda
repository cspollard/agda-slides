{-# OPTIONS --without-K --guardedness #-}

-- Executable: a deck with a non-default key binding, to `out/keys/` (`make keys`; checked in
-- the browser by `make test-keys`).  The binding is data: `init.js` carries a `keyboard`
-- option for exactly the keys where it differs from reveal.js's own table, `q` and the keys
-- that were dropped.

module Slides.Examples.KeysMain where

open import Data.List using (_∷_; [])
open import IO using (Main; run)

import Slides.Backend.Reveal as Reveal
open import Slides.Backend.Input using (Key; Mode; _≟Key_; bindKeys; arrowLeft; arrowRight; keyQ)
open import Slides.Backend.Reveal.Supports using (RCmd; nav; commonKinds; ⟨_⟩)
open import Slides.Input.Binding using (Decoder; on)
open import Slides.Input.Nav using (next; prev)
open import Slides.Core using (Deck)
open import Slides.DSL
open import Slides.Driver

-- `q` and the right arrow advance, the left arrow goes back, the common keys (Space, Home,
-- End, overview, ...) are reveal's; h j k l and the up and down arrows are dropped.
binding : Mode → Decoder Key RCmd
binding _ = bindKeys
  ( on _≟Key_ (⟨ keyQ ⟩ ∷ ⟨ arrowRight ⟩ ∷ []) (nav next)
  ∷ on _≟Key_ (⟨ arrowLeft ⟩ ∷ []) (nav prev)
  ∷ commonKinds )

keysDeck : Deck
keysDeck = do
  slide (do heading 2 "Keys"
            paragraph "first"
            pause
            paragraph "second")
  slide (heading 2 "Two")

main : Main
main = run (writeRevealDeck "out/keys" (record Reveal.defaultConfig { binding = binding }) keysDeck)
