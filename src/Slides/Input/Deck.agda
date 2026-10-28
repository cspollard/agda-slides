{-# OPTIONS --safe --without-K #-}

-- Decks that await commands (docs/Input.md, plan/Unify.md section 3).
--
-- `Slides.Core.Body` is unchanged: a body there is a program over `BlockC` and `pause`
-- is a layout command.  The vocabulary with awaited commands is a stratified wrapper:
--
--   BlockAwaitC X  = ProgC X: a block command (`Shape BlockC`), an awaited command `X`, or a label
--   DeckBlockC C   = BlockAwaitC (Nav ⊎ C) the vocabulary of a deck: navigation and extras `C`
--   Body⁺ X        = Prog X ⊤              a slide body that may await
--
-- `Slides.Steps.elab` takes a `Body` to a `Body⁺ (Nav ⊎ C)` (`pause ↦ await next`)
-- and `Supports.lowerDeck` lowers the awaited commands to a backend's.  A body that
-- awaits *is* a `Slides.Input.Prog` over the scene vocabulary `Shape BlockC` (the positions of
-- `BlockC` are all `⊤`), so `Slides.Input.Supports.lowerDeck` applies to it.

module Slides.Input.Deck where

open import Level using (0ℓ)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.String.Base using (String)
open import Data.Container.Core using (Container; Shape; _⇒_)
import Data.Container.Core as CC
open import Data.Container.Combinator using () renaming (_⊎_ to _⊎C_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)

open import Container.Lowering using (translate)
open import Slides.Core
open import Slides.Input (Shape BlockC) public using (Nav; next; prev; first; last; goto; gotoLabel; AwaitC; LabelC; ProgC; Prog)

BlockAwaitC : Set → Container 0ℓ 0ℓ
BlockAwaitC = ProgC

DeckBlockC : Set → Container 0ℓ 0ℓ
DeckBlockC C = BlockAwaitC (Nav ⊎ C)

Body⁺ : Set → Set
Body⁺ X = Prog X ⊤

-- The awaited commands, and the labels, as body commands.
awaitIn : ∀ {X : Set} → AwaitC X ⇒ BlockAwaitC X
CC._⇒_.shape    awaitIn x = inj₂ (inj₁ x)
CC._⇒_.position awaitIn   p = p

awaitB : ∀ {X : Set} → X → Body⁺ X
awaitB x = impure (inj₂ (inj₁ x) , λ _ → pure tt)

labelB : ∀ {X : Set} → String → Body⁺ X
labelB l = impure (inj₂ (inj₂ l) , λ _ → pure tt)
