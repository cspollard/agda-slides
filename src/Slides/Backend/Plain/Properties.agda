{-# OPTIONS --safe --without-K #-}

-- Structural properties of the plain rendering: one `<section class="slide">` per slide, with stacks flattened,
-- and that presenting a deck renders it as `steps` did (see `Slides.Backend.Reveal.Properties`).
module Slides.Backend.Plain.Properties where

open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Properties using (length-++; length-map; map-cong)
open import Data.String using () renaming (_++_ to _++ˢ_)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; cong₂; trans; _≗_)
open import Data.Container.Core using (Shape)
open import Data.Container.FreeMonad using (pure; impure)


open import Slides.Core
open import Slides.Steps using (steps)
open import Data.XML.Print using (renderXML)
open import Slides.Backend.HTML
open import Slides.Backend.Common

open import Slides.Backend.Plain
open import Slides.Input.Supports (Shape BlockC) using (Supports; NavTotal)
open Supports
open import Slides.Input.Nav using (next)
open import Slides.Lower using (presentBody)
open import Slides.Lower.Properties using (steps-pipeline)

------------------------------------------------------------------------
-- Structural properties

-- The number of slides: a stack contributes one slide per body.
countSlides : Deck → ℕ
countSlides (pure _)                  = 0
countSlides (impure (slide _ _ , k))  = suc (countSlides (k tt))
countSlides (impure (stack _ bs , k)) = length bs + countSlides (k tt)

-- One `<section class="slide">` per slide, with stacks flattened.
renderDeck-length : ∀ d → length (renderDeck d) ≡ countSlides d
renderDeck-length (pure tt)                  = refl
renderDeck-length (impure (slide _ _ , k))   = cong suc (renderDeck-length (k tt))
renderDeck-length (impure (stack o bs , k))  =
  trans (length-++ (map (slideSection o ∘ renderBody ∘ steps) bs))
        (cong₂ _+_ (length-map (slideSection o ∘ renderBody ∘ steps) bs) (renderDeck-length (k tt)))

------------------------------------------------------------------------
-- Presenting

renderDeckBy-cong : ∀ {f g : Body → Body} → f ≗ g → ∀ d → renderDeckBy f d ≡ renderDeckBy g d
renderDeckBy-cong h (pure tt)                 = refl
renderDeckBy-cong h (impure (slide o b , k))  =
  cong₂ _∷_ (cong (slideSection o ∘ renderBody) (h b)) (renderDeckBy-cong h (k tt))
renderDeckBy-cong h (impure (stack o bs , k)) =
  cong₂ _++_ (map-cong (λ b → cong (slideSection o ∘ renderBody) (h b)) bs) (renderDeckBy-cong h (k tt))

present-renderDeck : ∀ {C} (b : Supports C) → NavTotal b → ∀ d →
                     renderDeckBy (presentBody b) d ≡ renderDeck d
present-renderDeck b nt = renderDeckBy-cong (steps-pipeline b (nt next))

present-plain : ∀ {C} (b : Supports C) (nt : NavTotal b) cfg d →
                present b nt cfg d ≡ doctype ++ˢ renderXML (page cfg (renderDeck d))
present-plain b nt cfg d = cong (λ f → doctype ++ˢ renderXML (page cfg f)) (present-renderDeck b nt d)
