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
open import Data.Container.Core using (Container)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
import Data.Container.FreeMonad as FM

open import Slides.Literals public
open import Slides.Math using (Math)
open import Slides.Diagram using (Diagram)
open import Slides.Anim.Syntax using (Anim; Seg)
open import Slides.Anim.Render using (render)
open import Slides.Core using ()
open import Slides.Core hiding (heading; paragraph; bullets; code; displayMath; figure; notes; table; references; slide; stack; columns; box; fragment; pause; placed; diagram; animation; script; mount; classed)
import Slides.Core as Core
import Container.Interpret as Interpret
open import Container.Sum using (inl)

------------------------------------------------------------------------
-- `do`-notation (the overloaded literals are in `Slides.Literals`)

-- Sequencing is the free monad's bind, which works for every container
-- (content, body and deck programs alike), so `do` needs no instances.
open import Data.Container.FreeMonad using (_>>=_) public

infixl 1 _>>_
_>>_ : ∀ {s p} {C : Container s p} {X Y : Set} → C ⋆ X → C ⋆ Y → C ⋆ Y
m >> n = m >>= λ _ → n

-- Kleisli composition: components that take an argument and return a
-- program compose, `f >=> g = λ x → f x >>= g`.  The programs of a container
-- and these arrows form the Kleisli category of its free monad; the laws
-- hold up to `Container.Lowering._≈⋆_` (`bind-assoc≈`, `bind-pure≈`).
infixr 1 _>=>_
_>=>_ : ∀ {s p} {C : Container s p} {A B X : Set} →
        (A → C ⋆ B) → (B → C ⋆ X) → A → C ⋆ X
(f >=> g) x = f x >>= g

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

  diagram : Diagram → Content
  diagram d = cmd (Core.diagram d)

  animation : Diagram → List Diagram → Content
  animation d ds = cmd (Core.animation d ds)

  script : String → Content
  script js = cmd (Core.script js)

  mount : String → Content
  mount i = cmd (Core.mount i)

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

-- Content in a `<div class=…>`: the hook for a deck's own stylesheet (cards,
-- callouts, grids).  Several classes are separated by spaces.
classed : String → Content → Body
classed cls c = impure (inj₂ (Core.classed cls c) , λ _ → pure tt)

box : Text → Content → Body
box t c = impure (inj₂ (Core.box t c) , λ _ → pure tt)

-- Content in a box at (x, y) of size w × h, in percent of the slide.
placed : (x y w h : ℕ) → Content → Body
placed x y w h c = impure (inj₂ (Core.placed x y w h c) , λ _ → pure tt)

-- An inline vector diagram (see `Slides.Diagram`).
diagram : Diagram → Body
diagram d = liftContent (Content.diagram d)

-- Frames of an animation, one per step (see `Slides.Anim.Render`).
animation : Diagram → List Diagram → Body
animation d ds = liftContent (Content.animation d ds)

-- An animation (`Slides.Anim.Syntax`) as one step per tick: `animate name width a`;
-- `name` is unique in the deck and `width` the displayed percent.
animate : String → ℕ → Anim ℕ (Seg ℕ) → Body
animate n pct a = liftContent (Content.cmd (render n pct a))

-- JavaScript for the reveal.js and standalone backends, run once when its
-- slide is first shown (`slide` is the slide element); and an empty element
-- with an id for it to draw into.
script : String → Body
script js = liftContent (Content.script js)

mount : String → Body
mount i = liftContent (Content.mount i)

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
