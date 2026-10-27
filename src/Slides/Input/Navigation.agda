{-# OPTIONS --safe --without-K #-}

-- Running a deck under the navigation vocabulary.
--
-- A deck awaits `next` (that is what `pause` is); `prev`, `goto`, `first`, `last` and
-- `gotoLabel` are not awaited by the program but interpreted by `navM`, which keeps a
-- position `n` (the number of `next`s taken) and shows the deck machine replayed by that
-- many `next`s: history by replay, so going back needs no inverse of `step`.
--
--   nextCount p     the number of `await next` of p (the last position)
--   labelTable p    `label l` resolves to the number of `await next` before it
--                   (first occurrence wins); `nothing` for an unknown label
--   navM M len tbl  the machine a navigating backend runs
--   navDeck p       navM (machine p) (nextCount p) (labelTable p)
--
-- Laws: `Slides.Input.Navigation.Properties`.

module Slides.Input.Navigation (V : Set) where

open import Data.Bool.Base using (if_then_else_)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _⊓_)
open import Data.Product.Base using (_,_)
open import Data.String.Base using (String)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.Definitions using (DecidableEquality)
import Data.String.Properties as Str

open import Slides.Input V
open import Slides.Input.Machine V
open Machine

module _ {C : Set} where

  -- The position an awaited command advances: only `next` is a step.
  δ : Nav ⊎ C → ℕ
  δ (inj₁ next) = 1
  δ _           = 0

  nextCount : ∀ {A} → Deck C A → ℕ
  nextCount (pure _)                       = 0
  nextCount (impure (inj₁ _ , k))          = nextCount (k tt)
  nextCount (impure (inj₂ (inj₁ c) , k))   = δ c + nextCount (k tt)
  nextCount (impure (inj₂ (inj₂ _) , k))   = nextCount (k tt)

  -- `labelFrom n p`: the table of `p` when `n` nexts precede it.
  labelFrom : ∀ {A} → ℕ → Deck C A → String → Maybe ℕ
  labelFrom n (pure _)                       l = nothing
  labelFrom n (impure (inj₁ _ , k))          l = labelFrom n (k tt) l
  labelFrom n (impure (inj₂ (inj₁ c) , k))   l = labelFrom (n + δ c) (k tt) l
  labelFrom n (impure (inj₂ (inj₂ l′) , k))  l =
    if ⌊ l′ Str.≟ l ⌋ then just n else labelFrom n (k tt) l

  labelTable : ∀ {A} → Deck C A → String → Maybe ℕ
  labelTable = labelFrom 0

replay : ∀ {C} (M : Machine (Nav ⊎ C)) → ℕ → State M
replay M zero    = init M
replay M (suc n) = step M (replay M n) (inj₁ next)

module _ {C : Set} (M : Machine (Nav ⊎ C)) (len : ℕ) (labels : String → Maybe ℕ) where

  navStep : ℕ → Nav → ℕ
  navStep n next          = suc n ⊓ len
  navStep zero    prev    = zero
  navStep (suc n) prev    = n
  navStep n first         = zero
  navStep n last          = len
  navStep n (goto k)      = k ⊓ len
  navStep n (gotoLabel l) = maybe′ (_⊓ len) n (labels l)

  navM : Machine Nav
  navM = record { State = ℕ ; init = zero ; step = navStep ; view = λ n → view M (replay M n) }

module _ {C : Set} (d : DecidableEquality (Nav ⊎ C)) {A : Set} (p : Deck C A) where

  navDeck : Machine Nav
  navDeck = navM (machine d p) (nextCount p) (labelTable p)
