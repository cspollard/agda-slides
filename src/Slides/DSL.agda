{-# OPTIONS --safe --without-K #-}

-- Smart constructors and `do`-notation for decks.
--
--   deck = do
--     slide do
--       heading 1 "Title"
--       paragraph ("some " ∷ emph "marked up" ∷ " text")
--
-- The top-level commands build slide bodies (`Body`).  Inside `columns` and
-- `box` the content is a `Content` program; its commands are in the
-- `Content` submodule (`Content.heading`, `Content.paragraph`, …).
-- Commands taking running text come in two forms: the plain one takes a
-- `String`, the primed one (`paragraph′`, …) takes marked-up `Text`, a list of
-- `Inline`s (build them with `text`, `emph`, `strong`, `inlineMath`, `codeSpan`,
-- `link`).

module Slides.DSL where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
import Data.Container.FreeMonad as FM
open import Effect.Monad using (RawMonad)

open import Slides.Core hiding (heading; paragraph; bullets; code; displayMath; figure; notes; table; slide; stack; columns; box; fragment)
import Slides.Core as Core
import Container.Interpret as Interpret
open import Container.Sum using (inl)

------------------------------------------------------------------------
-- `do`-notation

instance
  contentMonad : RawMonad {f = 0ℓ} (ContentC ⋆_)
  contentMonad = FM.monad

  bodyMonad : RawMonad {f = 0ℓ} (BlockC ⋆_)
  bodyMonad = FM.monad

  deckMonad : RawMonad {f = 0ℓ} (DeckC ⋆_)
  deckMonad = FM.monad

open RawMonad {{...}} public using (_>>_; _>>=_)

------------------------------------------------------------------------
-- Content programs

module Content where
  cmd : ContentShape → Content
  cmd c = impure (c , λ _ → pure tt)

  plain : String → Text
  plain s = text s ∷ []

  heading′ : ℕ → Text → Content
  heading′ n t = cmd (Core.heading n t)

  heading : ℕ → String → Content
  heading n s = heading′ n (plain s)

  paragraph′ : Text → Content
  paragraph′ t = cmd (Core.paragraph t)

  paragraph : String → Content
  paragraph s = paragraph′ (plain s)

  bullets′ : List Text → Content
  bullets′ xs = cmd (Core.bullets false xs)

  bullets : List String → Content
  bullets xs = bullets′ (map plain xs)

  incremental′ : List Text → Content
  incremental′ xs = cmd (Core.bullets true xs)

  incremental : List String → Content
  incremental xs = incremental′ (map plain xs)

  code : (language source : String) → Content
  code l s = cmd (Core.code l s)

  displayMath : String → Content
  displayMath s = cmd (Core.displayMath s)

  figure′ : (src : String) → Text → Content
  figure′ s c = cmd (Core.figure s c)

  figure : (src caption : String) → Content
  figure s c = figure′ s (plain c)

  notes′ : Text → Content
  notes′ t = cmd (Core.notes t)

  notes : String → Content
  notes s = notes′ (plain s)

  table : (header : List Text) (rows : List (List Text)) → Content
  table h r = cmd (Core.table h r)

-- A content program as a slide body, along the injection `ContentC ⇒ BlockC`.
open Interpret.Translate 0ℓ 0ℓ ContentC BlockC inl using (translate)

liftContent : Content → Body
liftContent = translate

------------------------------------------------------------------------
-- Body commands

heading′ : ℕ → Text → Body
heading′ n t = liftContent (Content.heading′ n t)

heading : ℕ → String → Body
heading n s = liftContent (Content.heading n s)

paragraph′ : Text → Body
paragraph′ t = liftContent (Content.paragraph′ t)

paragraph : String → Body
paragraph s = liftContent (Content.paragraph s)

bullets′ : List Text → Body
bullets′ xs = liftContent (Content.bullets′ xs)

bullets : List String → Body
bullets xs = liftContent (Content.bullets xs)

incremental′ : List Text → Body
incremental′ xs = liftContent (Content.incremental′ xs)

incremental : List String → Body
incremental xs = liftContent (Content.incremental xs)

code : (language source : String) → Body
code l s = liftContent (Content.code l s)

displayMath : String → Body
displayMath s = liftContent (Content.displayMath s)

figure′ : (src : String) → Text → Body
figure′ s c = liftContent (Content.figure′ s c)

figure : (src caption : String) → Body
figure s c = liftContent (Content.figure s c)

notes′ : Text → Body
notes′ t = liftContent (Content.notes′ t)

notes : String → Body
notes s = liftContent (Content.notes s)

table : (header : List Text) (rows : List (List Text)) → Body
table h r = liftContent (Content.table h r)

columns : List Content → Body
columns cs = impure (inj₂ (Core.columns cs) , λ _ → pure tt)

-- Content that appears on a later step.
fragment : Content → Body
fragment c = impure (inj₂ (Core.fragment nothing c) , λ _ → pure tt)

fragmentWith : String → Content → Body
fragmentWith style c = impure (inj₂ (Core.fragment (just style) c) , λ _ → pure tt)

box′ : Text → Content → Body
box′ t c = impure (inj₂ (Core.box t c) , λ _ → pure tt)

box : String → Content → Body
box t c = box′ (Content.plain t) c

------------------------------------------------------------------------
-- Deck commands

deck-cmd : DeckShape → Deck
deck-cmd c = impure (c , λ _ → pure tt)

slideWith : SlideOptions → Body → Deck
slideWith o b = deck-cmd (Core.slide o b)

slide : Body → Deck
slide = slideWith defaultSlide

stackWith : SlideOptions → List Body → Deck
stackWith o bs = deck-cmd (Core.stack o bs)

stack : List Body → Deck
stack = stackWith defaultSlide

-- Options.
background : String → SlideOptions
background c = record defaultSlide { background = just c }

transition : String → SlideOptions
transition t = record defaultSlide { transition = just t }
