{-# OPTIONS --safe --without-K #-}

-- `pause` is `await next` (plan/Unify.md section 3).
--
-- Two passes reproduce `Slides.Steps.steps`:
--
--   elab     a Kleisli lowering `BlockC → DeckBlockC C` (`Container.Lowering.lower`) that
--            sends `pause` to `await next` and every other command to itself;
--   stepsBy  the pass with a mode, on a body that awaits: a command is wrapped in a
--            fragment (`wrapC`, `stepL` of `Slides.Steps`) once a *step* has been awaited.
--            Which awaited commands are steps is a parameter `step? : X → Bool`: `isNext`
--            for the deck vocabulary `Nav ⊎ C`, and its pull-back along the decoder for a
--            backend vocabulary (`Slides.Lower.Properties.steps-lowered`).
--
-- The bridge theorem `stepsBy-elab` (`Slides.Steps.Properties`) is
-- `stepsBy isNext (elab b) ≡ steps b`, so `Slides.Steps` keeps working unchanged.

module Slides.Steps.Input where

open import Data.Bool.Base using (Bool; true; false; _∨_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.List using (map)
open import Data.Container.Core using (Shape)
open import Data.Container.FreeMonad using (pure; impure; _>>=_)

open import Data.Maybe.Base using (Maybe; just; nothing)
open import Container.Lowering using (Lowering; lower)
open import Slides.Core
open import Slides.Input.Deck
open import Slides.Input.Supports (Shape BlockC) using (Supports)
open Supports
open import Slides.Steps using (wrapC; stepL)

-- Only `next` is a step; other awaited commands do not show anything.
isNext : ∀ {C : Set} → Nav ⊎ C → Bool
isNext (inj₁ next) = true
isNext _           = false

-- The steps of a backend vocabulary: the commands that decode to `next`.
isNextS : ∀ {C : Set} (b : Supports C) → S b → Bool
isNextS b s with dec b s
... | just (inj₁ next) = true
... | _                = false

------------------------------------------------------------------------
-- Elaboration: `pause ↦ await next`

elabS : ∀ {C : Set} → LayoutShape → Shape (DeckBlockC C)
elabS pause = inj₂ (inj₁ (inj₁ next))
elabS l     = inj₁ (inj₂ l)

elabL : ∀ {C : Set} → Lowering BlockC (DeckBlockC C)
elabL (inj₁ c) = impure (inj₁ (inj₁ c) , λ _ → pure tt)
elabL (inj₂ l) = impure (elabS l , λ _ → pure tt)

elab : ∀ {C : Set} → Body → Body⁺ (Nav ⊎ C)
elab = lower elabL

------------------------------------------------------------------------
-- The pass with a mode, on a body that awaits

module _ {X : Set} (step? : X → Bool) where

  -- Elaborate a body, starting in the given mode (`go` of `Slides.Steps`): an awaited
  -- command that is a step switches the mode on and disappears.
  goBy : Bool → Body⁺ X → Body
  goBy m (pure x)                      = pure x
  goBy m (impure (inj₁ (inj₁ c) , k))  = wrapC m c >>= λ _ → goBy m (k tt)
  goBy m (impure (inj₁ (inj₂ l) , k))  = proj₂ (stepL m l) >>= λ _ → goBy (proj₁ (stepL m l)) (k tt)
  goBy m (impure (inj₂ (inj₁ x) , k))  = goBy (m ∨ step? x) (k tt)
  goBy m (impure (inj₂ (inj₂ _) , k))  = goBy m (k tt)     -- a label shows nothing

  stepsBy : Body⁺ X → Body
  stepsBy = goBy false

  -- The mode after running a body from the given mode (`after` of `Slides.Steps`).
  afterBy : Bool → Body⁺ X → Bool
  afterBy m (pure _)                     = m
  afterBy m (impure (inj₁ (inj₁ _) , k)) = afterBy m (k tt)
  afterBy m (impure (inj₁ (inj₂ l) , k)) = afterBy (proj₁ (stepL m l)) (k tt)
  afterBy m (impure (inj₂ (inj₁ x) , k)) = afterBy (m ∨ step? x) (k tt)
  afterBy m (impure (inj₂ (inj₂ _) , k)) = afterBy m (k tt)
