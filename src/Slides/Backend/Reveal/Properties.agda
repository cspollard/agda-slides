{-# OPTIONS --safe --without-K #-}

-- Structural properties of the Reveal rendering: one top-level `<section>` per slide command, in order, and `renderDeck`
-- commutes with sequencing of decks.  Presenting a deck (`present`: `elab`, `lowerCmdBody`,
-- `stepsBy`) renders it as `steps` did, for every backend that supports `next`.
module Slides.Backend.Reveal.Properties where

open import Data.List using ([]; _∷_; _++_; map; length)
open import Data.List.Properties using (map-cong)
open import Data.Maybe.Base using (just)
open import Data.String using () renaming (_++_ to _++ˢ_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Data.Container.Core using (Shape)
open import Data.Container.FreeMonad using (pure; impure)
import Data.Container.FreeMonad as FM
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≗_; refl; cong; cong₂)



open import Slides.Core
open import Slides.Steps using (steps)
open import Data.XML.Print using (renderXML)
open import Slides.Backend.HTML
open import Slides.Backend.Common public

open import Slides.Backend.Reveal
open import Slides.Input.Supports (Shape BlockC) using (Supports; NavTotal)
open Supports
open import Slides.Input.Nav using (next)
open import Slides.Lower using (presentBody)
open import Slides.Lower.Properties using (steps-pipeline)

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

------------------------------------------------------------------------
-- Presenting

-- The deck algebra depends on the per-body pass only pointwise: one clause per slide
-- constructor, a `map` congruence for `stack`.
renderDeckBy-cong : ∀ {f g : Body → Body} → f ≗ g → ∀ d → renderDeckBy f d ≡ renderDeckBy g d
renderDeckBy-cong h (pure tt)                 = refl
renderDeckBy-cong h (impure (slide o b , k))  =
  cong₂ _∷_ (cong (section (slideAttrs o) ∘ renderBody) (h b)) (renderDeckBy-cong h (k tt))
renderDeckBy-cong h (impure (stack o bs , k)) =
  cong₂ _∷_ (cong (section (slideAttrs o)) (map-cong (λ b → cong (section [] ∘ renderBody) (h b)) bs))
            (renderDeckBy-cong h (k tt))

-- A backend that supports `next` presents a deck as the old renderer: `steps` per slide,
-- then render (`steps-pipeline` on each body).
present-renderDeck : ∀ {C} (b : Supports C) → NavTotal b → ∀ d →
                     renderDeckBy (presentBody b) d ≡ renderDeck d
present-renderDeck b nt = renderDeckBy-cong (steps-pipeline b (nt next))

present-reveal : ∀ {C} (b : Supports C) (nt : NavTotal b) cfg d →
                 present b nt cfg d ≡ prologue ++ˢ renderXML (page cfg (renderDeck d))
present-reveal b nt cfg d = cong (λ f → prologue ++ˢ renderXML (page cfg f)) (present-renderDeck b nt d)
