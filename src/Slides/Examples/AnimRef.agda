{-# OPTIONS --safe --without-K #-}

-- A deck for checking the page player against the frames Agda computes.  Each
-- animation is followed by its frames as ordinary diagrams (`frameDiagrams`, the very
-- list the animation is shipped from, named `ref-…`); `tests/browser/anim-ref.mjs`
-- rebuilds each frame in the page from the first frame and the edits and compares it
-- with the reference.

module Slides.Examples.AnimRef where

open import Data.List using (List; []; _∷_)
open import Data.Container.FreeMonad using (pure)

open import Slides.Core using (Body; Deck)
open import Slides.DSL
open import Slides.Diagram using (Diagram)
open import Slides.Diagram.Scalar using (natOps)
open import Slides.Anim.Footprint using (parI; ⊤-witness)
open import Slides.Anim.Render using (frameDiagrams)
open import Slides.Anim.Timeline using (timeline; frames)
open import Slides.Diagram.Syntax using (atop)
open import Slides.Examples.Intro using (mover; counter)
open import Slides.Examples.PairsHero using (hero)

private
  diagrams : List Diagram → Body
  diagrams []       = pure tt
  diagrams (d ∷ ds) = do diagram d; diagrams ds

  steps : Body
  steps = do
    animate "mover" 60 100 (parI natOps mover counter ∷ [])
    diagrams (frameDiagrams "ref-mover" 60 (timeline atop (frames natOps) (parI natOps mover counter)))

  loop : Body
  loop = do
    animateLoop "hero" 100 100 (hero 7)
    diagrams (frameDiagrams "ref-hero" 100 (timeline atop (frames natOps) (hero 7)))

deck : Deck
deck = do
  slide steps
  slide loop
