{-# OPTIONS --safe --without-K #-}

-- Embeddings with agreement (docs/Objects.md, map 3), as they bear on programs.
--
--   diagram-const   a diagram is the scene `pure d`, shown from 0 for ever at parameter 0; the
--                   program that never waits on it is a constant machine (`inject-const`)
--
-- The other two live with their subjects: deck as scene of scenes (`Slides.Deck.Read.deck-visible`)
-- and program as scene (`skip-inject`, `skip-bind` in `Slides.Program.Syntax`; `skip-elab`,
-- `pause-agree` in `Slides.Deck.Program`).

open import Slides.Scalar.Space using (Space)
open import Slides.Scalar.Time using (Time)

module Slides.Program.Embed {T : Set} (Sp : Space T) (Tm : Time T) {D : Set} (val : D → T → T)
       (tick-nonneg : ∀ n → Space._≤_ Sp (Space.0# Sp) (Time.tick Tm n)) where

open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ)
open import Relation.Nullary.Decidable using (dec-true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Container.FreeMonad using (pure)

open import Slides.Scene.Syntax using (Scene)
import Slides.Scene.Animation Sp Tm val as A
open Space Sp using (0#; _≤_; _≤?_)

-- a diagram, as a scene, is shown from time 0 on, laid out at the parameter 0
diagram-const : ∀ (l : A.Leaf) t → 0# ≤ t → A.frameAt (pure l) t ≡ just (A.leafLayout l 0#)
diagram-const l t le rewrite dec-true (0# ≤? t) le = refl

-- at a whole tick (the model fact is the hypothesis: ticks are non-negative)
diagram-frame : ∀ (l : A.Leaf) n → A.frame (pure l) n ≡ just (A.leafLayout l 0#)
diagram-frame l n = diagram-const l (Time.tick Tm n) (tick-nonneg n)
