{-# OPTIONS --safe --without-K #-}

-- Beamer-style `pause`: everything after a `pause` appears step by step.
--
-- A slide body is a scene (`Slides.Anim.Syntax`, the one temporal container `TimeC`) whose leaves are
-- its commands, and a step is a tick of the ℕ clock:
--
--   elab        `pause ↦ await next` (a Kleisli lowering `BlockC → DeckBlockC C`);
--   sceneBy     a program that awaits is the scene `show c ; k = c ∥ k` and `step ; k = Delay 1 k`,
--               where which awaited commands are steps is a parameter `step? : X → Bool`: `isNext`
--               for the deck vocabulary `Nav ⊎ C`, and its pull-back along the decoder for a
--               backend vocabulary (`Slides.Lower.Properties.scene-lowered`);
--   stepsBy     the page: the performance of the scene (`Slides.Anim.Perform`: each command with the
--               tick it starts at) with a command that starts after tick 0 wrapped in a fragment.
--
-- `steps` is the page of an elaborated body.  Backends apply it to each slide body before rendering.
-- What step `j` shows is the scene at tick `j` (`Slides.Steps.Properties`); the page keeps only
-- whether a command is shown from the start, so every later command is a fragment of its own (a
-- reveal.js click each), even two that share a tick.  Laws: `Slides.Steps.Properties`.

module Slides.Steps where

open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (foldr)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Container.Core using (Shape)
open import Data.Container.FreeMonad using (pure; impure; _>>=_)

open import Container.Lowering using (Lowering; lower)
open import Slides.Core
open import Slides.Input.Deck
open import Slides.Input.Supports (Shape BlockC) using (Supports)
open Supports
open import Slides.Anim.Syntax using (Scene; _∥ᵃ_; delay)
open import Slides.Anim.Perform using (perform)

------------------------------------------------------------------------
-- Elaboration: `pause ↦ await next`

-- Only `next` is a step; other awaited commands do not show anything.
isNext : ∀ {C : Set} → Nav ⊎ C → Bool
isNext (inj₁ next) = true
isNext _           = false

-- The steps of a backend vocabulary: the commands that decode to `next`.
isNextS : ∀ {C : Set} (b : Supports C) → S b → Bool
isNextS b s with dec b s
... | just (inj₁ next) = true
... | _                = false

elabS : ∀ {C : Set} → LayoutShape → Shape (DeckBlockC C)
elabS pause = inj₂ (inj₁ (inj₁ next))
elabS l     = inj₁ (inj₂ l)

elabL : ∀ {C : Set} → Lowering BlockC (DeckBlockC C)
elabL (inj₁ c) = impure (inj₁ (inj₁ c) , λ _ → pure tt)
elabL (inj₂ l) = impure (elabS l , λ _ → pure tt)

elab : ∀ {C : Set} → Body → Body⁺ (Nav ⊎ C)
elab = lower elabL

------------------------------------------------------------------------
-- The scene of a body, and its page

-- a command of a slide
Leaf : Set
Leaf = Shape BlockC

-- a step is a tick
later : ∀ {A} → Bool → Scene A → Scene A
later true  a = delay 1 a
later false a = a

-- (`nothing` is the end of the body: nothing shown)
sceneBy : ∀ {X : Set} → (X → Bool) → Body⁺ X → Scene (Maybe Leaf)
sceneBy step? (pure _)                      = pure nothing
sceneBy step? (impure (inj₁ c , k))         = pure (just c) ∥ᵃ sceneBy step? (k tt)
sceneBy step? (impure (inj₂ (inj₁ x) , k))  = later (step? x) (sceneBy step? (k tt))
sceneBy step? (impure (inj₂ (inj₂ _) , k))  = sceneBy step? (k tt)     -- a label shows nothing

private
  cmd : Leaf → Body
  cmd s = impure (s , λ _ → pure tt)

-- A command that starts after tick 0 is a fragment (content) or a `stepped` command (layout);
-- notes and scripts are not shown on the slide, so they never are.
emit : ℕ → Maybe Leaf → Body
emit _       nothing                  = pure tt
emit zero    (just s)                 = cmd s
emit (suc _) (just (inj₁ (notes t)))  = cmd (inj₁ (notes t))
emit (suc _) (just (inj₁ (script j))) = cmd (inj₁ (script j))
emit (suc _) (just (inj₁ c))          = cmd (inj₂ (fragment nothing (impure (c , λ _ → pure tt))))
emit (suc _) (just (inj₂ l))          = cmd (inj₂ (stepped nothing l))

-- The page of a scene: its commands in order, a late one a fragment.
page : Scene (Maybe Leaf) → Body
page a = foldr place (pure tt) (proj₂ (perform a))
  where place : ℕ × Maybe Leaf → Body → Body
        place (o , l) r = emit o l >>= λ _ → r

stepsBy : ∀ {X : Set} → (X → Bool) → Body⁺ X → Body
stepsBy step? p = page (sceneBy step? p)

steps : Body → Body
steps b = stepsBy (isNext {⊤}) (elab b)
