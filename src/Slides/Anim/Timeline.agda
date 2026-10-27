{-# OPTIONS --safe --without-K #-}

-- The frame-by-frame reading of an animation, and its laws.
--
-- A timeline is a list of frames, one per tick.  Over any frame type `F` with a
-- way `_⊙_` of putting two frames on top of each other:
--
--   * `Seq` is concatenation (`++`);
--   * `Par` is `merge`, which overlays frame by frame and lets the longer side run
--     on alone once the shorter has ended.  Running on alone is padding with a
--     unit, without needing one: `merge [] ys = ys`.
--
-- So `timeline` is `foldA` into `(List F, ++, merge)`.  For the diagram language
-- take `F = Dia S` and `_⊙_ = atop`; the laws of `atop` (`Slides.Diagram.Place.Properties.Laws`)
-- then transfer to the laws of `Par` once the frames are laid out.
--
-- Laws, with `_≡_` unless the frame operation is involved:
--   * `++` is associative with unit `[]`; `merge` has unit `[]` on both sides
--   * `merge` is associative when `_⊙_` is, commutative when `_⊙_` is
--   * the swap law: `(a ⨾ b) ∥ (c ⨾ d) = (a ∥ c) ⨾ (b ∥ d)` when `a` and `c` last
--     equally long (needs nothing of `_⊙_`)
--   * `length (merge a b) = max`, so `length ∘ timeline = dur` (`dur` is the
--     timeline's length: both are `foldA`s, and the leaf agrees)

module Slides.Anim.Timeline where

open import Data.List using (List; []; _∷_; _++_; map; applyUpTo)
import Slides.Anim.Track as T
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_+_; suc)

open import Data.Fin using (suc)
open import Data.Product using (proj₁; proj₂)
open import Data.Container.FreeMonad using (_⋆_)
open import Slides.Diagram.Syntax using (Dia)
open import Slides.Diagram.Scalar using (Ops)
open import Slides.Anim.Syntax

-- what is shown when at most one of two parts is running, or both: they go over each other
mergeM : ∀ {F : Set} → (F → F → F) → Maybe F → Maybe F → Maybe F
mergeM _⊙_ nothing  y        = y
mergeM _⊙_ x        nothing  = x
mergeM _⊙_ (just x) (just y) = just (x ⊙ y)

module _ {F : Set} (_⊙_ : F → F → F) where

  merge : List F → List F → List F
  merge []       ys       = ys
  merge (x ∷ xs) []       = x ∷ xs
  merge (x ∷ xs) (y ∷ ys) = (x ⊙ y) ∷ merge xs ys

  -- the timeline of an animation, from the frames of each leaf
  timeline : ∀ {T} → (T → List F) → AnimC ⋆ T → List F
  timeline leaf = foldA leaf _++_ merge


-- the diagram language: a segment shows its body at the parameter's value on each tick, frames overlay by `atop`
frames : ∀ {S} → Ops S → Seg S → List (Dia S)
frames O s = map (λ t → body O s (proj₂ sampled t)) (applyUpTo (λ i → i) (proj₁ sampled))
  where sampled = T.sample T.ℚLerp (track s)
