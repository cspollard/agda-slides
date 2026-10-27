{-# OPTIONS --safe --without-K #-}

-- What a backend supports (docs/Input.md).
--
--   Supports C     a backend vocabulary `S` (decidable equality), a partial embedding
--                  `inj : Nav ⊎ C → Maybe S` of the deck's commands into it and the
--                  decoder `dec : S → Maybe (Nav ⊎ C)` back, mutually inverse where defined
--                  (so `inj` is injective: two commands never share a backend command).
--   NavTotal s     evidence that every `Nav` command is supported.  `present` demands it,
--                  so a backend without navigation rejects decks (`¬NavTotal-print`).
--   lowerDeck      the deck as a program over `S`: a supported `await k` becomes
--                  `await (inj k)`, an unsupported one is skipped (the documented default),
--                  scenes and labels are kept.  It is `Container.Lowering.lower`.
--   skipDeck       the same default in the generic vocabulary (unsupported awaits removed).
--
--   command        from a physical input: read it as a backend command with a decoder
--                  `r : Decoder I S` (`Slides.Input.Binding`), then decode it with `dec`; an input
--                  that reads as nothing, or as a backend command with no `Nav ⊎ C` meaning, is
--                  `nothing`.
--
-- Soundness and the round trip `command-render`: `Slides.Input.Supports.Properties`.

module Slides.Input.Supports (V : Set) where

open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
open import Data.Product.Base using (_,_; Σ-syntax)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit.Base using (⊤; tt)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Container.Lowering using (Lowering; lower)
open import Slides.Input V
open import Slides.Input.Binding using (Decoder)

record Supports (C : Set) : Set₁ where
  field
    S       : Set
    _≟S_    : DecidableEquality S
    inj     : Nav ⊎ C → Maybe S
    dec     : S → Maybe (Nav ⊎ C)
    dec-inj : ∀ {k s} → inj k ≡ just s → dec s ≡ just k
    inj-dec : ∀ {k s} → dec s ≡ just k → inj k ≡ just s
open Supports

NavTotal : ∀ {C} → Supports C → Set
NavTotal b = ∀ n → Σ[ s ∈ S b ] inj b (inj₁ n) ≡ just s

command : ∀ {C I} (b : Supports C) → Decoder I (S b) → Decoder I (Nav ⊎ C)
command b r i = maybe′ (dec b) nothing (r i)

module _ {C : Set} (b : Supports C) where

  lowerOp : Lowering (ProgC (Nav ⊎ C)) (ProgC (S b))
  lowerOp (inj₁ v)         = impure (inj₁ v , pure)
  lowerOp (inj₂ (inj₁ k))  with inj b k
  ... | just s             = impure (inj₂ (inj₁ s) , pure)
  ... | nothing            = pure tt
  lowerOp (inj₂ (inj₂ l))  = impure (inj₂ (inj₂ l) , pure)

  lowerDeck : ∀ {A} → Deck C A → Prog (S b) A
  lowerDeck = lower lowerOp

  skipOp : Lowering (ProgC (Nav ⊎ C)) (ProgC (Nav ⊎ C))
  skipOp (inj₁ v)         = impure (inj₁ v , pure)
  skipOp (inj₂ (inj₁ k))  with inj b k
  ... | just s            = impure (inj₂ (inj₁ k) , pure)
  ... | nothing           = pure tt
  skipOp (inj₂ (inj₂ l))  = impure (inj₂ (inj₂ l) , pure)

  skipDeck : ∀ {A} → Deck C A → Deck C A
  skipDeck = lower skipOp

  -- Presenting a deck needs navigation.
  present : ∀ {A} → NavTotal b → Deck C A → Prog (S b) A
  present _ = lowerDeck

-- A print backend supports nothing, so it cannot present a deck.
printS : ∀ {C} → Supports C
printS = record { S = ⊥ ; _≟S_ = λ () ; inj = λ _ → nothing ; dec = λ () ; dec-inj = λ ()
                ; inj-dec = λ { {_} {()} } }

¬NavTotal-print : ∀ {C} → NavTotal (printS {C}) → ⊥
¬NavTotal-print t with t next
... | () , ()

-- A reveal-like backend: all of `Nav`, no extra command.
navOnlyS : ∀ {C} → Supports C
navOnlyS = record
  { S = Nav ; _≟S_ = _≟N_
  ; inj = [ just , (λ _ → nothing) ] ; dec = λ n → just (inj₁ n)
  ; dec-inj = λ { {inj₁ _} refl → refl }
  ; inj-dec = λ { refl → refl } }

navOnlyS-total : ∀ {C} → NavTotal (navOnlyS {C})
navOnlyS-total n = n , refl
