{-# OPTIONS --safe --without-K #-}

-- Spike: backends declare which commands they support and bind them to inputs.
--
--   Backend C I   a supported vocabulary `S`, a partial embedding `inj` of the deck
--                 commands `Nav ⊎ C` into it (injective where defined), and
--                 `bind : S → I` (`I` the physical inputs).
--   NavTotal b    the evidence that `b` supports all of `Nav`.  `present` requires it,
--                 so a backend without Nav cannot present a deck (`¬NavTotal-print`).
--   lowerDeck     a command the backend does not support is dropped: its `await` is
--                 skipped (`lowerOp-unsupported`), a supported one is renamed
--                 (`lowerOp-supported`).  It is `Container.Lowering.lower`.
--   conflict?     decidable check that a finite binding table is injective
--                 (two commands on one input is a conflict).

module Slides.Spike.Input.Backend (V : Set) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (all?) renaming (_≟_ to _≟F_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_; Σ-syntax)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Container.FreeMonad using (pure; impure; _⋆_)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (_→-dec_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Container.Lowering using (Lowering; lower)
open import Slides.Spike.Input.Prog V

record Backend (C : Set) (Input : Set) : Set₁ where
  field
    S   : Set
    inj : Nav ⊎ C → Maybe S
    inj-injective : ∀ {a b s} → inj a ≡ just s → inj b ≡ just s → a ≡ b
    bind : S → Input
open Backend

NavTotal : ∀ {C I} → Backend C I → Set
NavTotal b = ∀ n → Σ[ s ∈ S b ] inj b (inj₁ n) ≡ just s

module _ {C I : Set} (b : Backend C I) where

  -- One operation of a deck, lowered to the vocabulary of the backend.
  lowerOp : Lowering (ProgC (Nav ⊎ C)) (ProgC (S b))
  lowerOp (inj₁ v)                  = impure (inj₁ v , pure)
  lowerOp (inj₂ (inj₁ k))           with inj b k
  ... | just s                      = impure (inj₂ (inj₁ s) , pure)
  ... | nothing                     = pure tt
  lowerOp (inj₂ (inj₂ _))           = impure (inj₂ (inj₂ tt) , pure)

  lowerDeck : ∀ {A} → Deck C A → Prog (S b) A
  lowerDeck = lower lowerOp

  -- Presenting a deck needs navigation.
  present : ∀ {A} → NavTotal b → Deck C A → Prog (S b) A
  present _ = lowerDeck

  lowerOp-supported : ∀ k s → inj b k ≡ just s →
                      lowerOp (inj₂ (inj₁ k)) ≡ impure (inj₂ (inj₁ s) , pure)
  lowerOp-supported k s e rewrite e = refl

  lowerOp-unsupported : ∀ k → inj b k ≡ nothing → lowerOp (inj₂ (inj₁ k)) ≡ pure tt
  lowerOp-unsupported k e rewrite e = refl

-- A print backend supports nothing, so it cannot present a deck.
printB : ∀ {C} → Backend C ⊤
printB = record { S = ⊥ ; inj = λ _ → nothing ; inj-injective = λ () ; bind = λ () }

¬NavTotal-print : ∀ {C} → NavTotal (printB {C}) → ⊥
¬NavTotal-print t with t next
... | () , ()

-- A reveal-like backend: all of `Nav` and no extra command.
navOnlyB : ∀ {C} → Backend C ⊤
navOnlyB = record
  { S = Nav ; inj = λ { (inj₁ n) → just n ; (inj₂ _) → nothing }
  ; inj-injective = λ { {inj₁ _} {inj₁ _} refl refl → refl ; {inj₁ _} {inj₂ _} refl () ; {inj₂ _} {_} () _ }
  ; bind = λ _ → tt }

navOnlyB-total : ∀ {C} → NavTotal (navOnlyB {C})
navOnlyB-total n = n , refl

-- An extra command is dropped by this backend.
dropped : ∀ {C} (c : C) → lowerOp navOnlyB (inj₂ (inj₁ (inj₂ c))) ≡ pure tt
dropped c = refl

-- `pause` stays `await next`.
pause-kept : ∀ {C} → lowerDeck (navOnlyB {C}) pause ≡ await next
pause-kept = refl

------------------------------------------------------------------------
-- Conflicts at binding

-- A finite binding table from `n` commands to inputs.
conflict? : ∀ {n} {I : Set} → DecidableEquality I → (t : Fin n → I) →
            Dec (∀ i j → t i ≡ t j → i ≡ j)
conflict? _≟_ t = all? λ i → all? λ j → (t i ≟ t j) →-dec (i ≟F j)

-- Bound commands are distinct inputs exactly when the table is injective and the
-- embedding is.
bound-injective : ∀ {C I} (b : Backend C I) →
  (∀ {s s′} → bind b s ≡ bind b s′ → s ≡ s′) →
  ∀ {a a′ s s′} → inj b a ≡ just s → inj b a′ ≡ just s′ → bind b s ≡ bind b s′ → a ≡ a′
bound-injective b bi {a} {a′} e e′ eq with bi eq
... | refl = inj-injective b e e′
