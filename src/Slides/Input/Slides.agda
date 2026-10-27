{-# OPTIONS --safe --without-K #-}

-- The slides of a deck as one program, with a label per slide (docs/Input.md, "Slide labels").
--
-- A physical `goto` addresses a slide (`#/intro`, `#3`), but `Slides.Input.Navigation` moves by
-- *position*, the number of `next`s taken.  The bridge is a label at the start of every slide:
--
--   slides d        the slides of a deck in order (a stack is flattened as `Backend.Plain` does;
--                   its label, if any, names its first slide), each with its user label
--   autoLabel i     the label of slide `i` (from 0): the decimal numeral of `i + 1`, which is
--                   what plain's `#n` says
--   deckBody ss     one body: `label (autoLabel i)`, the user label if any, the elaborated slide,
--                   and an `await next` between consecutive slides (a `next` at the end of a
--                   slide goes to the next one)
--   deckProg d      `toProg` of it: a `Slides.Input.Deck` program, so `navDeck`, `labelTable`
--                   and `Supports.present` apply
--
-- `Slides.Input.Slides.Properties`: `labelTable (deckProg d)` is the slide-start table
-- (`slide-table`), and the label of slide `i` resolves to the position where it starts
-- (`auto-start`).

module Slides.Input.Slides where

open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Show using (showInBase)
open import Data.Product.Base using (_×_; _,_)
open import Data.String.Base using (String)
open import Data.Sum.Base using (_⊎_; inj₁)
open import Data.Unit.Base using (⊤; tt)
open import Data.Container.FreeMonad using (pure; impure; _>>=_)

open import Slides.Core
open import Slides.Input.Deck
open import Slides.Steps.Input using (elab)

-- A slide: its user label and its body.
Slide : Set
Slide = Maybe String × Body

stackSlides : Maybe String → List Body → List Slide
stackSlides l []       = []
stackSlides l (b ∷ bs) = (l , b) ∷ map (nothing ,_) bs

slides : Deck → List Slide
slides (pure _)                     = []
slides (impure (slide o b , k))     = (SlideOptions.label o , b) ∷ slides (k tt)
slides (impure (stack o bs , k))    = stackSlides (SlideOptions.label o) bs ++ slides (k tt)

autoLabel : ℕ → String
autoLabel i = showInBase 10 (suc i)

module _ {C : Set} where

  userK : Maybe String → Body⁺ (Nav ⊎ C) → Body⁺ (Nav ⊎ C)
  userK nothing  k = k
  userK (just l) k = labelB l >>= λ _ → k

  -- slide `i`, then `k`
  slideK : ℕ → Slide → Body⁺ (Nav ⊎ C) → Body⁺ (Nav ⊎ C)
  slideK i (o , b) k = labelB (autoLabel i) >>= λ _ → userK o (elab b >>= λ _ → k)

  -- the slides from `i` on, each after a `next`
  rest : ℕ → List Slide → Body⁺ (Nav ⊎ C)
  rest i []       = pure tt
  rest i (s ∷ ss) = awaitB (inj₁ next) >>= λ _ → slideK i s (rest (suc i) ss)

  deckBody : List Slide → Body⁺ (Nav ⊎ C)
  deckBody []       = pure tt
  deckBody (s ∷ ss) = slideK 0 s (rest 1 ss)

  deckProg : Deck → Prog (Nav ⊎ C) ⊤
  deckProg d = toProg (deckBody (slides d))
