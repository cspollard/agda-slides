{-# OPTIONS --safe --without-K #-}

-- Control for ../NonUniformBoth.agda: MUST typecheck (every phase has acts of the same lengths).

module UniformBothOk where

open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ)

open import Slides.Deck.DSL
open import Slides.Deck.Anim using (Anim; frame′; txt; defaultStyle)

acts : ℕ → List Anim
acts _ = frame′ 2 (txt 20 "a" defaultStyle) ∷ []

ok : Body
ok = animateBoth "ok" 100 100 2 acts
