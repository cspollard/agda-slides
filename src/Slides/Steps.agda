{-# OPTIONS --safe --without-K #-}

-- Beamer-style `pause`: everything after a `pause` appears step by step.
--
-- `pause` is an ordinary (layout) command that renders as nothing.  Its
-- meaning is given by this elaboration of a body into a pause-free body:
-- a pass with a mode (`false` until the first `pause`, `true` after) that
-- wraps every later command in a fragment.  Content commands become
-- `fragment` commands, other layout commands are `stepped`, and `notes` are
-- left alone (they are not shown on the slide).  The mode flows through
-- sequencing, so a `pause` in one component affects the commands that follow
-- it, including those of later components; `go-bind` (`Slides.Steps.Properties`) states
-- exactly how.  `Slides.Steps.Input` is the same pass after the elaboration
-- `pause ↦ await next`.
--
-- Backends apply `steps` to each slide body before rendering.

module Slides.Steps where

open import Data.Bool using (Bool; true; false; _∨_; if_then_else_)
open import Data.Maybe using (nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Container.FreeMonad using (pure; impure; _>>=_)

open import Slides.Core

private
  content : ContentShape → Body
  content c = impure (inj₁ c , λ _ → pure tt)

  layout : LayoutShape → Body
  layout l = impure (inj₂ l , λ _ → pure tt)

-- Wrap a command for the current mode.
wrapC : Bool → ContentShape → Body
wrapC false c         = content c
wrapC true  (notes t) = content (notes t)
wrapC true  (script j) = content (script j)
wrapC true  c         = layout (fragment nothing (impure (c , λ _ → pure tt)))

private
  wrapL : Bool → LayoutShape → Body
  wrapL false l = layout l
  wrapL true  l = layout (stepped nothing l)

-- What a layout command does in a mode: the mode afterwards, and its
-- replacement.  (A `pause` switches the mode on and disappears.)
stepL : Bool → LayoutShape → Bool × Body
stepL m l = (m ∨ isPause l) , (if isPause l then pure tt else wrapL m l)
  where
    isPause : LayoutShape → Bool
    isPause pause = true
    isPause _     = false

-- Elaborate a body, starting in the given mode.
go : Bool → Body → Body
go m (pure x)                = pure x
go m (impure (inj₁ c , k))   = wrapC m c >>= λ _ → go m (k tt)
go m (impure (inj₂ l , k))   = proj₂ (stepL m l) >>= λ _ → go (proj₁ (stepL m l)) (k tt)

steps : Body → Body
steps = go false

-- The mode after running a body from the given mode.
after : Bool → Body → Bool
after m (pure _)              = m
after m (impure (inj₁ _ , k)) = after m (k tt)
after m (impure (inj₂ l , k)) = after (proj₁ (stepL m l)) (k tt)
