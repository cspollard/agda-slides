{-# OPTIONS --safe --without-K #-}

-- Smart constructors and `do`-notation for decks.
--
--   deck = do
--     slide′ do
--       heading 1 "Title"
--       paragraph "text"
--     slide′ do …

module Slides.DSL where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Container.Core using (Container)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
import Data.Container.FreeMonad as FM
open import Data.Product using (_,_)
open import Effect.Monad using (RawMonad)

open import Slides.Core hiding (heading; paragraph; bullets; code; displayMath; figure; notes; slide; stack)
import Slides.Core as Core

-- `do`-notation works at both levels through instance arguments.
instance
  contentMonad : RawMonad {f = 0ℓ} (ContentC ⋆_)
  contentMonad = FM.monad

  deckMonad : RawMonad {f = 0ℓ} (DeckC ⋆_)
  deckMonad = FM.monad

open RawMonad {{...}} public using (_>>_; _>>=_)

-- A single command as a program.
content : ContentShape → Body
content c = impure (c , λ _ → pure tt)

deck-cmd : DeckShape → Deck
deck-cmd c = impure (c , λ _ → pure tt)

------------------------------------------------------------------------
-- Content commands

heading : ℕ → String → Body
heading n s = content (Core.heading n s)

paragraph : String → Body
paragraph s = content (Core.paragraph s)

bullets : List String → Body
bullets = λ xs → content (Core.bullets false xs)

incremental : List String → Body
incremental xs = content (Core.bullets true xs)

code : (language source : String) → Body
code l s = content (Core.code l s)

displayMath : String → Body
displayMath s = content (Core.displayMath s)

figure : (src caption : String) → Body
figure s c = content (Core.figure s c)

notes : String → Body
notes s = content (Core.notes s)

------------------------------------------------------------------------
-- Deck commands

slide : Body → Deck
slide b = deck-cmd (Core.slide b)

stack : List Body → Deck
stack bs = deck-cmd (Core.stack bs)
