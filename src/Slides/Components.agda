{-# OPTIONS --safe --without-K #-}

-- Reusable slide components.
--
-- A component is an ordinary function into the free monad: its parameters
-- go in, a `Body` (or `Deck`) comes out, and components compose with `>>`
-- and `>>=`.  The backend respects composition: rendering a sequence is the
-- concatenation of the renderings (`renderBody-bind`,
-- `renderDeck-bind` in `Slides.Backend.Reveal`).

module Slides.Components where

open import Data.List using (List; _∷_; [])

open import Slides.Core using (Body; Deck; Content; Text; K)
open import Slides.DSL

-- Decorators: `Body K → Body K`.

titled : Text → Body K → Body K
titled t b = heading 2 t >> b

withNotes : Text → Body K → Body K
withNotes n b = b >> notes n

-- Slide bodies.

titleBody : (title subtitle author : Text) → Body K
titleBody t s a = do
  heading 1 t
  paragraph s
  paragraph a

bulletBody : Text → List Text → Body K
bulletBody t xs = titled t (bullets xs)

incrementalBody : Text → List Text → Body K
incrementalBody t xs = titled t (incremental xs)

twoColumn : Text → Content → Content → Body K
twoColumn t l r = titled t (columns (l ∷ r ∷ []))

resultsTable : Text → (header : List Text) → List (List Text) → Body K
resultsTable t header rows = titled t (table header rows)

-- Whole slides.

sectionSlide : Text → Deck K
sectionSlide t = slideWith (background "#1b1b2f") (heading 1 t)

titleSlide : (title subtitle author : Text) → Deck K
titleSlide t s a = slide (titleBody t s a)
