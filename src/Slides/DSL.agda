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
open import Data.Container.Core using (_⇒_; Container)
open import Data.String using (String)
open import Data.Unit using (⊤; tt) public
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
import Data.Container.FreeMonad as FM
open import Effect.Monad using (RawMonad)

open import Slides.Literals public
open import Slides.Math using (Math)
open import Slides.Core hiding (heading; paragraph; bullets; code; displayMath; figure; notes; table; references; slide; stack; columns; box; fragment; pause)
import Slides.Core as Core
-- instances needed to render decks are in scope wherever the DSL is
open import Slides.Core using (NoCap; steppable-⊥; steppable-⊕) public
import Container.Interpret as Interpret

------------------------------------------------------------------------
-- `do`-notation (the overloaded literals are in `Slides.Literals`)

instance
  contentMonad : RawMonad {f = 0ℓ} (ContentC ⋆_)
  contentMonad = FM.monad

  bodyMonad : ∀ {K} → RawMonad {f = 0ℓ} (BlockOf K ⋆_)
  bodyMonad = FM.monad

  deckMonad : ∀ {K} → RawMonad {f = 0ℓ} (DeckC K ⋆_)
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
injContent : ∀ K → ContentC ⇒ BlockOf K
injContent K = record { shape = λ s → inj₁ (inj₁ s) ; position = λ x → x }

liftContent : Content → Body K
liftContent {K} = translate
  where open Interpret.Translate 0ℓ 0ℓ ContentC (BlockOf K) (injContent K) using (translate)

-- Layout and capability commands.
layoutCmd : LayoutShape → Body K
layoutCmd l = impure (inj₁ (inj₂ l) , λ _ → pure tt)

capCmd : K → Body K
capCmd s = impure (inj₂ s , λ _ → pure tt)

------------------------------------------------------------------------
-- Body commands

heading : ℕ → Text → Body K
heading n t = liftContent (Content.heading n t)

paragraph : Text → Body K
paragraph t = liftContent (Content.paragraph t)

bullets : List Text → Body K
bullets xs = liftContent (Content.bullets xs)

incremental : List Text → Body K
incremental xs = liftContent (Content.incremental xs)

code : (language source : String) → Body K
code l s = liftContent (Content.code l s)

displayMath : Math → Body K
displayMath m = liftContent (Content.displayMath m)

figureUnchecked : (src : String) → Text → Body K
figureUnchecked s c = liftContent (Content.figureUnchecked s c)

notes : Text → Body K
notes t = liftContent (Content.notes t)

table : (header : List Text) (rows : List (List Text)) → Body K
table h r = liftContent (Content.table h r)

columns : List Content → Body K
columns cs = layoutCmd (Core.columns cs)

-- Content that appears on a later step.
fragment : Content → Body K
fragment c = layoutCmd (Core.fragment nothing c)

fragmentWith : String → Content → Body K
fragmentWith style c = layoutCmd (Core.fragment (just style) c)

-- Everything after a `pause` in the same body appears step by step.
pause : Body K
pause = layoutCmd Core.pause

box : Text → Content → Body K
box t c = layoutCmd (Core.box t c)

------------------------------------------------------------------------
-- Deck commands

deck-cmd : DeckShape (Body K) → Deck K
deck-cmd c = impure (c , λ _ → pure tt)

slideWith : SlideOptions → Body K → Deck K
slideWith o b = deck-cmd (Core.slide o b)

slide : Body K → Deck K
slide = slideWith defaultSlide

stackWith : SlideOptions → List (Body K) → Deck K
stackWith o bs = deck-cmd (Core.stack o bs)

stack : List (Body K) → Deck K
stack = stackWith defaultSlide

-- Options.
background : String → SlideOptions
background c = record defaultSlide { background = just c }

transition : String → SlideOptions
transition t = record defaultSlide { transition = just t }
