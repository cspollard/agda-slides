{-# OPTIONS --safe --without-K #-}

-- The slide vocabulary as containers.
--
-- A deck is a program in the free monad over `DeckC`; a slide's content is
-- a program in the free monad over `ContentC`.  Nesting is stratified rather
-- than recursive: the shape of the `slide` command *contains* a content
-- program (a `Body`), so no container mentions itself and strict positivity
-- is not an issue.  Backends are algebras for each level (see
-- `Container.Interpret`).
--
-- All commands have a single continuation (`Position = ⊤`).

module Slides.Core where

open import Level using (0ℓ)
open import Data.Bool using (Bool)
open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.Unit using (⊤)
open import Data.Container.Core using (Container; _▷_)
open import Data.Container.FreeMonad using (_⋆_)

------------------------------------------------------------------------
-- Content inside a slide

data ContentShape : Set where
  heading     : (level : ℕ) → String → ContentShape
  paragraph   : String → ContentShape
  bullets     : (incremental : Bool) → List String → ContentShape
  code        : (language source : String) → ContentShape
  displayMath : String → ContentShape
  figure      : (src caption : String) → ContentShape
  notes       : String → ContentShape

ContentC : Container 0ℓ 0ℓ
ContentC = ContentShape ▷ λ _ → ⊤

-- The content of one slide.
Body : Set
Body = ContentC ⋆ ⊤

------------------------------------------------------------------------
-- The deck

data DeckShape : Set where
  -- a horizontal slide
  slide : Body → DeckShape
  -- a vertical stack of slides (reveal.js nested sections)
  stack : List Body → DeckShape

DeckC : Container 0ℓ 0ℓ
DeckC = DeckShape ▷ λ _ → ⊤

Deck : Set
Deck = DeckC ⋆ ⊤
