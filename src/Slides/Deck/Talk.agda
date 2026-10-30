{-# OPTIONS --safe --without-K #-}

-- A talk: a list of parts (a slide, or a vertical stack of slides, each with its `Look`),
-- the free monoid on them; backends are monoid homomorphisms from it (`Slides.Backend.Render`).
-- `slides` forgets the grouping, so a stack is layout only:
--   `slides-++`    slides (xs ++ ys) ≡ slides xs ++ slides ys
--   `slides-stack` slidesP (vstack l ss) ≡ toList ss
-- A stack's label is its first slide's.

module Slides.Deck.Talk where

open import Data.List.Base using (List; []; _∷_; _++_; concatMap; map)
open import Data.List.NonEmpty using (List⁺; _∷_; toList)
import Data.List.Properties as ListP
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.String.Base using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Slides.Deck.Syntax

-- the options of a slide's `<section>` (a CSS colour, a reveal.js transition) and its label
record Look : Set where
  constructor look
  field
    background transition label : Maybe String

plainLook : Look
plainLook = look nothing nothing nothing

data Part : Set where
  solo   : Look → Slide → Part
  vstack : Look → List⁺ Slide → Part

Talk : Set
Talk = List Part

slidesP : Part → List Slide
slidesP (solo _ s)   = s ∷ []
slidesP (vstack _ ss) = toList ss

slides : Talk → List Slide
slides = concatMap slidesP

slides-++ : ∀ xs ys → slides (xs ++ ys) ≡ slides xs ++ slides ys
slides-++ = ListP.concatMap-++ slidesP

slides-stack : ∀ l ss → slidesP (vstack l ss) ≡ toList ss
slides-stack l ss = refl

-- reveal.js moves on a grid when a talk has a vertical stack, linearly otherwise
data Mode : Set where
  linear stacked : Mode

modeP : Part → Mode
modeP (solo _ _)   = linear
modeP (vstack _ _) = stacked

mode : Talk → Mode
mode []       = linear
mode (p ∷ ps) with modeP p
... | stacked = stacked
... | linear  = mode ps
