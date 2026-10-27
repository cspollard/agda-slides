{-# OPTIONS --safe --without-K #-}

-- Spike: a two-step deck `show "a" ; pause ; show "b"`, run by `refl`.

module Slides.Spike.Input.Example where

open import Data.List.Base using (_∷_; [])
open import Data.String.Base using (String)
open import Data.Sum.Base using (_⊎_; inj₁)
open import Data.Sum.Properties using (≡-dec)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Nullary using (yes)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Slides.Spike.Input.Prog String
open import Slides.Spike.Input.Machine String
open Machine
open import Slides.Spike.Input.Nav String using (_≟N_)

-- The deck has no extra commands (`C = ⊤`).
_≟D_ : DecidableEquality (Nav ⊎ ⊤)
_≟D_ = ≡-dec _≟N_ (λ _ _ → yes refl)

open Sem _≟D_

deck : Deck ⊤ ⊤
deck = show "a" ⨾ pause ⨾ show "b"

M : Machine (Nav ⊎ ⊤)
M = machine deck

view-0 : view M (init M) ≡ "a" ∷ []
view-0 = refl

view-1 : view M (step M (init M) (inj₁ next)) ≡ "a" ∷ "b" ∷ []
view-1 = refl

-- any other command is ignored
view-prev : view M (step M (init M) (inj₁ prev)) ≡ "a" ∷ []
view-prev = refl
