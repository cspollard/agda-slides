{-# OPTIONS --safe --without-K #-}

-- Reusable slide components.
--
-- A component is an ordinary function into the free monad: its parameters
-- go in, a `Body` (or `Deck`) comes out, and components compose with `>>`
-- and `>>=`.  The backend respects composition: rendering a sequence is the
-- concatenation of the renderings (`renderBody-bind`,
-- `renderDeck-bind` in `Slides.Backend.Reveal`).

module Slides.Components where

open import Data.List using (List; _∷_; []; map)
open import Data.String using (String)

open import Slides.Core using (Body; Deck; Content; Text; text)
open import Slides.DSL

-- Decorators: `Body → Body`.

titled : String → Body → Body
titled t b = heading 2 t >> b

withNotes : String → Body → Body
withNotes n b = b >> notes n

-- Slide bodies.

titleBody : (title subtitle author : String) → Body
titleBody t s a = do
  heading 1 t
  paragraph s
  paragraph a

bulletBody : String → List String → Body
bulletBody t xs = titled t (bullets xs)

incrementalBody : String → List String → Body
incrementalBody t xs = titled t (incremental xs)

twoColumn : String → Content → Content → Body
twoColumn t l r = titled t (columns (l ∷ r ∷ []))

resultsTable : String → (header : List String) → List (List String) → Body
resultsTable t header rows =
  titled t (table (map plain header) (map (map plain) rows))
  where
    plain : String → Text
    plain s = text s ∷ []

-- Whole slides.

sectionSlide : String → Deck
sectionSlide t = slideWith (background "#1b1b2f") (heading 1 t)

titleSlide : (title subtitle author : String) → Deck
titleSlide t s a = slide (titleBody t s a)
