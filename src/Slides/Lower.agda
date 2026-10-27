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
-- The commands a deck awaits are lowered the same way (`lowerCmd`): along a backend's
-- `Supports` a supported `await k` becomes `await (inj k)` and an unsupported one is
-- skipped (the documented default).  Commands are awaited only at the top of a body
-- (`Slides.Input.Deck`), so no layout or content command nests one: the lifting to
-- bodies (`lowerCmdBody`) leaves everything else alone.
--
-- Lowerings compose with `_⋙_` before they are lifted, so a backend that
-- lacks several features applies one combined lowering.  Interpreting the
-- lowered deck equals interpreting the original with the pulled-back
-- algebra (`Container.Lowering.Fusion.lower-fusion`).

module Slides.Lower where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Container.Core using (Shape)
open import Data.Container.FreeMonad using (pure; impure)

open import Container.Lowering
open import Container.Sum using (inl; inr)
open import Slides.Core
open import Slides.Diagram using (Diagram)
open import Slides.Input.Deck
open import Slides.Input.Supports (Shape BlockC) using (Supports)
open Supports
open import Slides.Steps.Input using (elab; stepsBy; isNextS)

------------------------------------------------------------------------
-- Content lowerings

-- Drop the speaker notes.
stripNotes : Lowering ContentC ContentC
stripNotes (notes _) = pure tt
stripNotes a         = ret a

-- Replace each diagram (and animation) by a one-line placeholder, for a backend
-- without vector graphics.
diagramPlaceholder : Lowering ContentC ContentC
diagramPlaceholder (diagram d) =
  impure (paragraph (text "[diagram]" ∷ []) , pure)
diagramPlaceholder (animation d ds _ _) =
  impure (paragraph (text "[animation]" ∷ []) , pure)
diagramPlaceholder (paramAnimation d ds _ _ _) =
  impure (paragraph (text "[animation]" ∷ []) , pure)
diagramPlaceholder a = ret a

-- The frame an animation comes to rest on once all its steps have played: the
-- last of the `rests` (within the first phase, for steps over a loop), and the
-- first frame when there are no steps (a loop).  `nth` clamps to the last frame.
nth : Diagram → List Diagram → ℕ → Diagram
nth d []       _       = d
nth d (f ∷ fs) zero    = d
nth d (f ∷ fs) (suc n) = nth f fs n

lastRest : List ℕ → ℕ
lastRest []       = 0
lastRest (n ∷ []) = n
lastRest (_ ∷ ns) = lastRest ns

finalFrame : Diagram → List Diagram → Play → Diagram
finalFrame d ds (onSteps rs) = nth d ds (lastRest rs)
finalFrame d ds looping      = d
finalFrame d ds (both rs _)  = nth d ds (lastRest rs)

-- For a backend that cannot play animations (print, a script-free page): the
-- animation as a still of its final frame, the picture the audience is left with.
animationFinal : Lowering ContentC ContentC
animationFinal (animation d ds _ p) = impure (diagram (finalFrame d ds p) , pure)
animationFinal (paramAnimation d ds _ _ p) = impure (diagram (finalFrame d ds p) , pure)
animationFinal a                    = ret a

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

------------------------------------------------------------------------
-- Command lowerings

module _ {C : Set} (b : Supports C) where

  -- A supported command is renamed, an unsupported one is skipped.
  lowerCmd : Lowering (AwaitC (Nav ⊎ C)) (AwaitC (S b))
  lowerCmd k with inj b k
  ... | just s  = impure (s , pure)
  ... | nothing = pure tt

  -- Lower the awaited commands of a body; blocks are kept.
  lowerCmdBlock : Lowering (DeckBlockC C) (BlockAwaitC (S b))
  lowerCmdBlock (inj₁ s) = impure (inj₁ s , pure)
  lowerCmdBlock (inj₂ k) = lower (embed inr) (lowerCmd k)

  lowerCmdBody : Body⁺ (Nav ⊎ C) → Body⁺ (S b)
  lowerCmdBody = lower lowerCmdBlock

  -- What a backend does with a slide body: elaborate `pause` to `await next`, lower the
  -- awaited commands to the backend's, then step.  It is `Slides.Steps.steps` for a backend
  -- that supports `next` (`steps-pipeline`).
  presentBody : Body → Body
  presentBody x = stepsBy (isNextS b) (lowerCmdBody (elab x))
