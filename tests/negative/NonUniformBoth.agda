{-# OPTIONS --safe --without-K #-}

-- Must NOT typecheck: phase 1 of the loop has an act of a different length than phase 0, so the
-- phases are not copies of one set of steps.
-- EXPECT: Unsolved metas
-- Control: controls/UniformBothOk.agda.

module NonUniformBoth where

open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)

open import Slides.Deck.DSL
open import Slides.Deck.Anim using (Anim; frame′; lit; txt; defaultStyle)

acts : ℕ → List Anim
acts zero = frame′ 1 (txt 20 "a" defaultStyle) ∷ []
acts _    = frame′ 2 (txt 20 "a" defaultStyle) ∷ []

bad : Body
bad = animateBoth "bad" 100 100 2 acts
