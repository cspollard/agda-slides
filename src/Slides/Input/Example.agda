{-# OPTIONS --safe --without-K #-}

-- Worked examples, checked by `refl` (not imported by any executable).  The scene vocabulary
-- is `String`, so the views can be read.

module Slides.Input.Example where

open import Data.List.Base using (_∷_; [])
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁)
open import Data.Sum.Properties using (≡-dec)
open import Data.Unit.Base using (⊤)
open import Relation.Nullary using (yes)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
-- Over plain strings, to read the views.
module Strings where
  open import Data.String.Base using (String)
  open import Slides.Input String
  open import Slides.Input.Machine String
  open Machine
  open import Slides.Input.Navigation String
  open import Slides.Input.Supports String
  open Supports

  dK : _
  dK = ≡-dec _≟N_ (λ (_ _ : ⊤) → yes refl)

  deck : Deck ⊤ ⊤
  deck = show "a" ⨾ pause ⨾ label "mid" ⨾ show "b" ⨾ pause ⨾ show "c"

  N : Machine Nav
  N = navDeck dK deck

  table : labelTable deck "mid" ≡ just 1
  table = refl

  count : nextCount deck ≡ 2
  count = refl

  view-0 : view N (init N) ≡ "a" ∷ []
  view-0 = refl

  view-label : view N (step N (init N) (gotoLabel "mid")) ≡ "a" ∷ "b" ∷ []
  view-label = refl

  view-last : view N (step N (init N) last) ≡ "a" ∷ "b" ∷ "c" ∷ []
  view-last = refl

  view-back : view N (step N (step N (init N) last) prev) ≡ "a" ∷ "b" ∷ []
  view-back = refl

  -- A reveal-like backend keeps the pauses; an extra command is skipped.
  pause-kept : lowerDeck (navOnlyS {⊤}) pause ≡ await next
  pause-kept = refl

-- Slide labels on a deck of `Slides.Core` (`Slides.Examples.Labels`).
module Slides where
  open import Data.List.Base using (length)
  open import Data.Container.Core using (Shape)
  open import Slides.Core using (BlockC)
  open import Slides.Input.Slides
  open import Slides.Input.Navigation (Shape BlockC)
  open import Slides.Examples.Labels using (labels)

  -- intro, details (one pause), unnamed, more (two slides), end
  _ : length (slides labels) ≡ 6
  _ = refl

  -- slide `i` starts after the pauses and `next`s before it
  opaque
    unfolding autoLabel

    _ : labelTable (deckBody {⊤} (slides labels)) (autoLabel 0) ≡ just 0
    _ = refl
    _ : labelTable (deckBody {⊤} (slides labels)) (autoLabel 2) ≡ just 3
    _ = refl
    _ : labelTable (deckBody {⊤} (slides labels)) (autoLabel 5) ≡ just 6
    _ = refl

    -- a user label is the start of its slide; a stack's label is that of its first slide
    _ : labelTable (deckBody {⊤} (slides labels)) "details" ≡ just 1
    _ = refl
    _ : labelTable (deckBody {⊤} (slides labels)) "more" ≡ just 4
    _ = refl
    _ : labelTable (deckBody {⊤} (slides labels)) "end" ≡ just 6
    _ = refl
    _ : labelTable (deckBody {⊤} (slides labels)) "nowhere" ≡ nothing
    _ = refl
