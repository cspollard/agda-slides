{-# OPTIONS --safe --without-K #-}

-- Structural properties of the plain rendering: one `<section class="slide">` per slide, with stacks flattened.
module Slides.Backend.Plain.Properties where

open import Data.List using (List; _++_; map; length)
open import Data.List.Properties using (length-++; length-map)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; trans)
open import Data.Container.FreeMonad using (pure; impure)


open import Slides.Core
open import Slides.Steps using (steps)
open import Slides.Backend.HTML
open import Slides.Backend.Common

open import Slides.Backend.Plain

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
  where open import Relation.Binary.PropositionalEquality.Core using (cong₂)
