{-# OPTIONS --safe --without-K #-}

-- Embeddings with agreement (docs/Objects.md, map 3).
--
--   diagram as constant scene   a diagram is the scene `pure d`: present from time 0 for ever,
--                               at its parameter 0 (`diagram-const`), and the program that
--                               never waits on it is a constant machine (`Slides.Program.Sem.inject-const`
--                               at `pure d`);
--   deck as scene of scenes     `Slides.Deck.Read.flat-visible`, `deck-visible`: reading the
--                               nested scene is reading the flattened one; the deck machine
--                               shows it (`Slides.Deck.Machine`);
--   program as scene            `skip` (`Slides.Program.Syntax`): the retraction `skip-inject`,
--                               the monad morphism `skip-bind`, and for decks `skip-elab`
--                               (`Slides.Deck.Program`): forgetting the waits of the elaborated
--                               scene removes its delays; the machine shows the same
--                               accumulated chunks tick by tick (`pause-agree`).
--
-- Only the first has content of its own and lives here.

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
