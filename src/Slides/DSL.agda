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
-- Running text is `Text`, a list of `Inline`s (`text`, `emph`, `strong`,
-- `inlineMath`, `codeSpan`, `link`); a bare string literal is plain text.
-- Use `plain` to turn a `String` variable into `Text`.

module Slides.DSL where

open import Level using (0ℓ)
open import Agda.Builtin.FromString using (IsString; fromString) public
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.String using (String)
import Data.String.Literals
open import Data.Unit using (⊤; tt) public
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
import Data.Container.FreeMonad as FM
open import Effect.Monad using (RawMonad)

open import Slides.Core hiding (heading; paragraph; bullets; code; displayMath; figure; notes; table; slide; stack; columns; box; fragment)
import Slides.Core as Core
import Container.Interpret as Interpret
open import Container.Sum using (inl)

------------------------------------------------------------------------
-- Overloaded string literals and `do`-notation
--
-- A string literal at type `Text` or `Inline` is plain text.  Agda resolves
-- the literal's side condition with the instance `tt : ⊤`, which must be in
-- scope where the literal is written, and so must `fromString`; both are
-- re-exported from here.

instance
  -- once literals are overloaded, `String` literals need an instance too
  isStringString : IsString String
  isStringString = Data.String.Literals.isString

  isStringInline : IsString Inline
  isStringInline = record { Constraint = λ _ → ⊤ ; fromString = λ s → text s }

  isStringText : IsString Text
  isStringText = record { Constraint = λ _ → ⊤ ; fromString = λ s → text s ∷ [] }

  contentMonad : RawMonad {f = 0ℓ} (ContentC ⋆_)
  contentMonad = FM.monad

  bodyMonad : RawMonad {f = 0ℓ} (BlockC ⋆_)
  bodyMonad = FM.monad

  deckMonad : RawMonad {f = 0ℓ} (DeckC ⋆_)
  deckMonad = FM.monad

open RawMonad {{...}} public using (_>>_; _>>=_)

plain : String → Text
plain s = text s ∷ []

------------------------------------------------------------------------
-- Content programs

module Content where
  cmd : ContentShape → Content
  cmd c = impure (c , λ _ → pure tt)

  heading : ℕ → Text → Content
  heading n t = cmd (Core.heading n t)

  paragraph : Text → Content
  paragraph t = cmd (Core.paragraph t)

  bullets : List Text → Content
  bullets xs = cmd (Core.bullets false xs)

  incremental : List Text → Content
  incremental xs = cmd (Core.bullets true xs)

  code : (language source : String) → Content
  code l s = cmd (Core.code l s)

  displayMath : String → Content
  displayMath s = cmd (Core.displayMath s)

  figure : (src : String) → Text → Content
  figure s c = cmd (Core.figure s c)

  notes : Text → Content
  notes t = cmd (Core.notes t)

  table : (header : List Text) (rows : List (List Text)) → Content
  table h r = cmd (Core.table h r)

-- A content program as a slide body, along the injection `ContentC ⇒ BlockC`.
open Interpret.Translate 0ℓ 0ℓ ContentC BlockC inl using (translate)

liftContent : Content → Body
liftContent = translate

------------------------------------------------------------------------
-- Body commands

heading : ℕ → Text → Body
heading n t = liftContent (Content.heading n t)

paragraph : Text → Body
paragraph t = liftContent (Content.paragraph t)

bullets : List Text → Body
bullets xs = liftContent (Content.bullets xs)

incremental : List Text → Body
incremental xs = liftContent (Content.incremental xs)

code : (language source : String) → Body
code l s = liftContent (Content.code l s)

displayMath : String → Body
displayMath s = liftContent (Content.displayMath s)

figure : (src : String) → Text → Body
figure s c = liftContent (Content.figure s c)

notes : Text → Body
notes t = liftContent (Content.notes t)

table : (header : List Text) (rows : List (List Text)) → Body
table h r = liftContent (Content.table h r)

columns : List Content → Body
columns cs = impure (inj₂ (Core.columns cs) , λ _ → pure tt)

-- Content that appears on a later step.
fragment : Content → Body
fragment c = impure (inj₂ (Core.fragment nothing c) , λ _ → pure tt)

fragmentWith : String → Content → Body
fragmentWith style c = impure (inj₂ (Core.fragment (just style) c) , λ _ → pure tt)

box : Text → Content → Body
box t c = impure (inj₂ (Core.box t c) , λ _ → pure tt)

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
