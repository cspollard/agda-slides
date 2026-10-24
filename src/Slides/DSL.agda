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
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.String using (String)
open import Data.Unit using (⊤; tt) public
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
import Data.Container.FreeMonad as FM
open import Effect.Monad using (RawMonad)

open import Slides.Literals public
open import Slides.Math using (Math)
open import Slides.Core hiding (heading; paragraph; bullets; code; displayMath; figure; notes; table; references; slide; stack; columns; box; fragment; pause)
import Slides.Core as Core
import Container.Interpret as Interpret
open import Container.Sum using (inl)

------------------------------------------------------------------------
-- `do`-notation (the overloaded literals are in `Slides.Literals`)

instance
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

  displayMath : Math → Content
  displayMath m = cmd (Core.displayMath m)

  -- unchecked: see `Slides.Resources` for the checked `figure`
  figureUnchecked : (src : String) → Text → Content
  figureUnchecked s c = cmd (Core.figure s c)

  notes : Text → Content
  notes t = cmd (Core.notes t)

  table : (header : List Text) (rows : List (List Text)) → Content
  table h r = cmd (Core.table h r)

  references : List (String × Text) → Content
  references rs = cmd (Core.references rs)

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

displayMath : Math → Body
displayMath m = liftContent (Content.displayMath m)

figureUnchecked : (src : String) → Text → Body
figureUnchecked s c = liftContent (Content.figureUnchecked s c)

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

-- Everything after a `pause` in the same body appears step by step.
pause : Body
pause = impure (inj₂ Core.pause , λ _ → pure tt)

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
