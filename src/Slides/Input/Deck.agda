{-# OPTIONS --safe --without-K #-}

-- Decks that await commands (docs/Input.md, plan/Unify.md section 3).
--
-- `Slides.Core.Body` is unchanged: a body there is a program over `BlockC` and `pause`
-- is a layout command.  The vocabulary with awaited commands is a stratified wrapper:
--
--   BlockAwaitC X  = BlockC ⊎ AwaitC X     a block command, or an awaited command `X`
--   DeckBlockC C   = BlockAwaitC (Nav ⊎ C) the vocabulary of a deck: navigation and extras `C`
--   Body⁺ X        = BlockAwaitC X ⋆ ⊤     a slide body that may await
--   DeckC⁺ X       = slides whose bodies are `Body⁺ X`
--
-- `Slides.Steps.Input.elab` takes a `Body` to a `Body⁺ (Nav ⊎ C)` (`pause ↦ await next`)
-- and `Slides.Lower.lowerCmdDeck` lowers the awaited commands to a backend's.  A body is
-- a `Slides.Input.Prog` over the scene vocabulary `Shape BlockC` through `toProg`, so
-- `Slides.Input.Supports.lowerDeck` applies to it.

module Slides.Input.Deck where

open import Level using (0ℓ)
open import Data.List using (List)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤)
open import Data.Container.Core using (Container; Shape; _▷_; _⇒_)
import Data.Container.Core as CC
open import Data.Container.Combinator using () renaming (_⊎_ to _⊎C_)
open import Data.Container.FreeMonad using (_⋆_)

open import Container.Lowering using (translate)
open import Slides.Core
open import Slides.Input (Shape BlockC) public using (Nav; next; prev; first; last; goto; gotoLabel; AwaitC; ProgC; Prog)

BlockAwaitC : Set → Container 0ℓ 0ℓ
BlockAwaitC X = BlockC ⊎C AwaitC X

DeckBlockC : Set → Container 0ℓ 0ℓ
DeckBlockC C = BlockAwaitC (Nav ⊎ C)

Body⁺ : Set → Set
Body⁺ X = BlockAwaitC X ⋆ ⊤

data DeckShape⁺ (X : Set) : Set where
  slide⁺ : SlideOptions → Body⁺ X → DeckShape⁺ X
  stack⁺ : SlideOptions → List (Body⁺ X) → DeckShape⁺ X

DeckC⁺ : Set → Container 0ℓ 0ℓ
DeckC⁺ X = DeckShape⁺ X ▷ λ _ → ⊤

Deck⁺ : Set → Set
Deck⁺ X = DeckC⁺ X ⋆ ⊤

-- A body that awaits is a program of `Slides.Input` with scenes `Shape BlockC`.
toProgC : ∀ {X : Set} → BlockAwaitC X ⇒ ProgC X
CC._⇒_.shape    toProgC (inj₁ s) = inj₁ s
CC._⇒_.shape    toProgC (inj₂ x) = inj₂ (inj₁ x)
CC._⇒_.position toProgC {inj₁ (inj₁ _)} p = p
CC._⇒_.position toProgC {inj₁ (inj₂ _)} p = p
CC._⇒_.position toProgC {inj₂ _}        p = p

toProg : ∀ {X : Set} → Body⁺ X → Prog X ⊤
toProg = translate toProgC
