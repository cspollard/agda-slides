{-# OPTIONS --safe --without-K #-}

-- The `Placed` capability: content at a fixed position on the slide.
--
-- `placed x y w h c` puts the content program `c` in a box whose left edge,
-- top edge, width and height are given as whole percentages of the slide
-- (0–100).  It is optional: a deck using it has type `Deck K` with
-- `Placed ⊑ K`, and a backend must provide `HTMLCap Placed` (see
-- `Slides.Backend.Placed`).  After a `pause` a placed box appears on a later
-- step, like a fragment.

module Slides.Capability.Placed where

open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ)

open import Slides.Core
open import Slides.DSL using (capCmd)

data Placed : Set where
  -- (appears on a later step) left top width height content
  place : Bool → (x y w h : ℕ) → Content → Placed

instance
  steppable-Placed : Steppable Placed
  steppable-Placed = record { later = λ { (place _ x y w h c) → place true x y w h c } }

-- A box at (x, y) of size w × h, in percent of the slide.
placed : {{_ : Placed ⊑ K}} → (x y w h : ℕ) → Content → Body K
placed x y w h c = capCmd (inj (place false x y w h c))
