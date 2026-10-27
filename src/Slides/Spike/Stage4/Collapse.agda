{-# OPTIONS --safe --without-K #-}

-- STAGE 4 SPIKE: does `Body⁺ X` collapse into `Prog X ⊤`?  `goBy` of `Slides.Steps.Input`,
-- verbatim, on `Prog` over the scene vocabulary `Shape BlockC`: same patterns, `k tt` reduces.

module Slides.Spike.Stage4.Collapse where

open import Data.Bool.Base using (Bool; false; _∨_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Container.Core using (Shape)
open import Data.Container.FreeMonad using (pure; impure; _>>=_)

open import Slides.Core
open import Slides.Input (Shape BlockC) using (Prog)
open import Slides.Steps using (wrapC; stepL)

module _ {X : Set} (step? : X → Bool) where
  goBy : Bool → Prog X _ → Body
  goBy m (pure x)                      = pure x
  goBy m (impure (inj₁ (inj₁ c) , k))  = wrapC m c >>= λ _ → goBy m (k tt)
  goBy m (impure (inj₁ (inj₂ l) , k))  = proj₂ (stepL m l) >>= λ _ → goBy (proj₁ (stepL m l)) (k tt)
  goBy m (impure (inj₂ (inj₁ x) , k))  = goBy (m ∨ step? x) (k tt)
  goBy m (impure (inj₂ (inj₂ _) , k))  = goBy m (k tt)
