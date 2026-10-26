{-# OPTIONS --safe --without-K #-}

-- Structural properties of the Reveal rendering: one top-level `<section>` per slide command, in order, and `renderDeck`
-- commutes with sequencing of decks.
module Slides.Backend.Reveal.Properties where

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Nat using (ℕ; suc)
open import Data.Maybe using (Maybe)
open import Data.Product using (_,_)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Data.Container.FreeMonad using (pure; impure)
import Data.Container.FreeMonad as FM
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong)
import Data.List.Relation.Binary.Pointwise as PW

open import Data.Container.Relation.Binary.Pointwise
  using () renaming (_,_ to _,ₚ_)

open import Data.JSON.AST using (JSON)
import Data.Sign.Base as Sign
import Data.Integer.Base as ℤ

open import Container.FreeMonad.Algebraic using (module Alg)
open import Slides.Core
open import Slides.Steps using (steps)
open import Slides.Backend.HTML
open import Slides.Backend.Common public

open import Slides.Backend.Reveal

------------------------------------------------------------------------
-- Structural properties of the rendering

-- The number of slide commands (slides and stacks) in a deck.
count : Deck → ℕ
count (pure _)         = 0
count (impure (_ , k)) = suc (count (k tt))

-- One top-level `<section>` per slide command, in order.
renderDeck-length : ∀ d → length (renderDeck d) ≡ count d
renderDeck-length (pure tt)                = refl
renderDeck-length (impure (slide _ _ , k)) = cong suc (renderDeck-length (k tt))
renderDeck-length (impure (stack _ _ , k)) = cong suc (renderDeck-length (k tt))

renderDeck-bind : ∀ (d₁ d₂ : Deck) →
                  renderDeck (d₁ FM.>>= λ _ → d₂) ≡ renderDeck d₁ ++ renderDeck d₂
renderDeck-bind (pure tt)                 d₂ = refl
renderDeck-bind (impure (slide o b , k))  d₂ =
  cong (section (slideAttrs o) (renderBody (steps b)) ∷_) (renderDeck-bind (k tt) d₂)
renderDeck-bind (impure (stack o bs , k)) d₂ =
  cong (section (slideAttrs o) (map (section [] ∘ renderBody ∘ steps) bs) ∷_) (renderDeck-bind (k tt) d₂)
