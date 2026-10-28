{-# OPTIONS --safe --without-K #-}

-- Decks: a scene of scenes over content leaves.
--
--   Body         what an author writes for one slide: blocks and `pause`s (the free monoid)
--   chunks b     the Beamer split: the blocks between pauses; fragment index = start tick
--   slideScene   one slide as a scene over `Flow` leaves on the tick clock:
--                chunk i is present from tick i, so a pause is `Delay 1` under `Par`
--                (`chunk i ∥ delay 1 (chunk (i+1) ∥ ...)`), and the slide is held for its
--                `1 + pauses` ticks, one per state a presenter passes through
--   Deck         a scene whose leaves are slides, in sequence (`Seq`): the slide leaf is read
--                for its own duration (`Slides.Deck.Read`), so a deck is a scene of scenes
--   flat         the deck as one scene over `Flow` leaves: substitution of each slide's scene
--                for its leaf, which is `_>>=_` (nesting by substitution)
--
-- Why chunks: the legacy elaboration (`Slides.Steps`) threaded a mode through a body and wrapped
-- every later command in a fragment of its own; here the meaning is the start tick of the chunk
-- (`Slides.Deck.Read.index`), and a body's pauses are not rewritten at all.
--
--   chunks-++    a pause in one body affects the content of the next (the legacy `go-bind`)

module Slides.Deck.Syntax where

open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.List.NonEmpty using (List⁺; _∷_; toList)
import Data.List.NonEmpty as L⁺
open import Data.Maybe.Base using (Maybe)
open import Data.Nat.Base using (ℕ; suc)
open import Data.String.Base using (String)
open import Data.Container.FreeMonad using (pure; _>>=_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

open import Slides.Scene.Syntax
open import Slides.Deck.Content

data Item : Set where
  block : Block → Item
  pause : Item

Body : Set
Body = List Item

addBlock : Block → List⁺ Flow → List⁺ Flow
addBlock b (c ∷ cs) = (b ∷ c) ∷ cs

chunks : Body → List⁺ Flow
chunks []              = [] ∷ []
chunks (block b ∷ xs)  = addBlock b (chunks xs)
chunks (pause ∷ xs)    = [] ∷ toList (chunks xs)

pauses : Body → ℕ
pauses []              = 0
pauses (block _ ∷ xs)  = pauses xs
pauses (pause ∷ xs)    = suc (pauses xs)

-- one tick per chunk
length-chunks : ∀ b → L⁺.length (chunks b) ≡ suc (pauses b)
length-chunks []             = refl
length-chunks (block _ ∷ xs) with chunks xs | length-chunks xs
... | c ∷ cs | e = e
length-chunks (pause ∷ xs)   = cong suc (length-chunks xs)

-- the chunks of a concatenation: the last chunk of the first body joins the first of the second
glueL : Flow → List Flow → List⁺ Flow → List⁺ Flow
glueL c []       (d ∷ ds) = (c ++ d) ∷ ds
glueL c (e ∷ es) ys       = c ∷ toList (glueL e es ys)

glue : List⁺ Flow → List⁺ Flow → List⁺ Flow
glue (c ∷ cs) = glueL c cs

private
  glue-nil : ∀ ys → glue ([] ∷ []) ys ≡ ys
  glue-nil (d ∷ ds) = refl

  addBlock-glue : ∀ b xs ys → addBlock b (glue xs ys) ≡ glue (addBlock b xs) ys
  addBlock-glue b (c ∷ [])     (d ∷ ds) = refl
  addBlock-glue b (c ∷ e ∷ es) ys       = refl

chunks-++ : ∀ xs ys → chunks (xs ++ ys) ≡ glue (chunks xs) (chunks ys)
chunks-++ []             ys = sym (glue-nil (chunks ys))
chunks-++ (block b ∷ xs) ys rewrite chunks-++ xs ys = addBlock-glue b (chunks xs) (chunks ys)
chunks-++ (pause ∷ xs)   ys with chunks xs | chunks (xs ++ ys) | chunks-++ xs ys
... | c ∷ cs | _ | refl = refl

------------------------------------------------------------------------
-- Scenes

record Slide : Set where
  constructor slide
  field
    label  : Maybe String
    chunkL : List⁺ Flow

mkSlide : Maybe String → Body → Slide
mkSlide l b = slide l (chunks b)

-- the number of ticks (states) of a slide
ticks : Slide → ℕ
ticks s = L⁺.length (Slide.chunkL s)

-- chunk i from tick i
chunkFrom : Flow → List Flow → Scene ℕ ⊥ Flow
chunkFrom c []       = pure c
chunkFrom c (d ∷ ds) = pure c ∥ delay 1 (chunkFrom d ds)

chunkScene : List⁺ Flow → Scene ℕ ⊥ Flow
chunkScene (c ∷ cs) = chunkFrom c cs

slideScene : Slide → Scene ℕ ⊥ Flow
slideScene s = hold (ticks s) (chunkScene (Slide.chunkL s))

Deck : Set
Deck = Scene ℕ ⊥ Slide

-- slides in sequence
deckFrom : Slide → List Slide → Deck
deckFrom s []       = pure s
deckFrom s (t ∷ ts) = pure s ⨾ deckFrom t ts

deckOf : List⁺ Slide → Deck
deckOf (s ∷ ss) = deckFrom s ss

flat : Deck → Scene ℕ ⊥ Flow
flat d = d >>= slideScene
