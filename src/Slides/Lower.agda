{-# OPTIONS --safe --without-K #-}

-- Lowerings of the slide vocabulary.
--
-- A lowering (`Container.Lowering`) rewrites each command of a vocabulary
-- as a program over another (or the same) one; `lower` extends it to whole
-- programs.  A lowering of *content* commands is lifted here to every
-- place content occurs (slide bodies, columns, boxes, fragments, placed
-- boxes), and then to whole decks:
--
--     lowerDeck : Lowering ContentC ContentC → Deck → Deck
--
-- Lowerings compose with `_⋙_` before they are lifted, so a backend that
-- lacks several features applies one combined lowering.  Interpreting the
-- lowered deck equals interpreting the original with the pulled-back
-- algebra (`Container.Lowering.Fusion.lower-fusion`).

module Slides.Lower where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
open import Data.Container.FreeMonad using (pure; impure)

open import Container.Lowering
open import Container.Sum using (inl)
open import Slides.Core

------------------------------------------------------------------------
-- Content lowerings

-- Drop the speaker notes.
stripNotes : Lowering ContentC ContentC
stripNotes (notes _) = pure tt
stripNotes a         = ret a

-- Replace each diagram by a one-line placeholder naming it, for a backend
-- without vector graphics.
diagramPlaceholder : Lowering ContentC ContentC
diagramPlaceholder (diagram d) =
  impure (paragraph (text "[diagram]" ∷ []) , pure)
diagramPlaceholder (animation d ds _ _) =
  impure (paragraph (text "[animation]" ∷ []) , pure)
diagramPlaceholder a = ret a

------------------------------------------------------------------------
-- Lifting to the layout, block and deck levels

module _ (l : Lowering ContentC ContentC) where

  -- Lower the content nested in a layout command.
  layout : LayoutShape → LayoutShape
  layout (columns cs)     = columns (map (lower l) cs)
  layout (box t c)        = box t (lower l c)
  layout (fragment s c)   = fragment s (lower l c)
  layout pause            = pause
  layout (classed k c)    = classed k (lower l c)
  layout (placed x y w h c) = placed x y w h (lower l c)
  layout (stepped s sh)   = stepped s (layout sh)

  -- Lower the content commands of a body, and the content nested in its
  -- layout commands.
  block : Lowering BlockC BlockC
  block (inj₁ c)  = lower (embed inl) (l c)
  block (inj₂ sh) = impure (inj₂ (layout sh) , pure)

  -- Lower the bodies of the slides of a deck.
  deck : Lowering DeckC DeckC
  deck (slide o b)  = impure (slide o (lower block b) , pure)
  deck (stack o bs) = impure (stack o (map (lower block) bs) , pure)

lowerBody : Lowering ContentC ContentC → Body → Body
lowerBody l = lower (block l)

lowerDeck : Lowering ContentC ContentC → Deck → Deck
lowerDeck l = lower (deck l)

-- Drop the scripts and the elements they draw into, for a backend without
-- JavaScript.
stripScripts : Lowering ContentC ContentC
stripScripts (script _) = pure tt
stripScripts (mount _)  = pure tt
stripScripts a          = ret a
