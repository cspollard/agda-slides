{-# OPTIONS --safe --without-K #-}

-- Reusable slide components.
--
-- A component is an ordinary function into the free monad: its parameters
-- go in, a `Body` (or `Deck`) comes out, and components compose with `>>`
-- and `>>=`.  The backend respects composition: rendering a sequence is the
-- concatenation of the renderings (`renderBody-bind` in `Slides.Backend.Common.Properties`,
-- `renderDeck-bind` in `Slides.Backend.Reveal.Properties`).

module Slides.Components where

open import Data.List using (List; _∷_; [])

open import Slides.Core using (Body; Deck; Content; Text)
open import Slides.DSL

-- Decorators: `Body → Body`.

titled : Text → Body → Body
titled t b = heading 2 t >> b

withNotes : Text → Body → Body
withNotes n b = b >> notes n

-- Slide bodies.

titleBody : (title subtitle author : Text) → Body
titleBody t s a = do
  heading 1 t
  paragraph s
  paragraph a

bulletBody : Text → List Text → Body
bulletBody t xs = titled t (bullets xs)

incrementalBody : Text → List Text → Body
incrementalBody t xs = titled t (incremental xs)

twoColumn : Text → Content → Content → Body
twoColumn t l r = titled t (columns (l ∷ r ∷ []))

resultsTable : Text → (header : List Text) → List (List Text) → Body
resultsTable t header rows = titled t (table header rows)

-- Whole slides.

sectionSlide : Text → Deck
sectionSlide t = slideWith (background "#1b1b2f") (heading 1 t)

titleSlide : (title subtitle author : Text) → Deck
titleSlide t s a = slide (titleBody t s a)
