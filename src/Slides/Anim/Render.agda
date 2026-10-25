{-# OPTIONS --safe --without-K #-}

-- From an animation to the frames a backend shows.
--
-- `timeline` (merging with `atop`) gives one `Dia ℕ` per tick; each is laid out
-- and compiled to a `Diagram`.  All frames get the size of the largest, so the
-- picture does not jump when a smaller frame replaces a larger one (frames are
-- anchored at the top left, as drawn).  The result is the `animation` command:
-- the first frame and the rest, with `n` ticks giving `n` frames.  A zero-length
-- animation is one empty frame.

module Slides.Anim.Render where

open import Data.List using (List; []; _∷_; map; foldr)
open import Data.Nat using (ℕ; _⊔_; suc)
open import Data.Nat.Show using (show)
open import Data.String using (String) renaming (_++_ to _++ˢ_)

open import Slides.Core using (ContentShape; animation)
open import Slides.Diagram using (Diagram; module Diagram)
open import Slides.Diagram.Syntax using (Dia; atop; spacer)
open import Slides.Diagram.Layout using (compile)
open import Slides.Anim.Syntax using (Anim; Seg)
open import Slides.Anim.Timeline using (timeline; frames)

private
  -- name each frame `name-i`
  compileFrames : String → ℕ → ℕ → List (Dia ℕ) → List Diagram
  compileFrames name pct i []       = []
  compileFrames name pct i (f ∷ fs) = compile (name ++ˢ "-" ++ˢ show i) pct f ∷ compileFrames name pct (suc i) fs

  maxWidth maxHeight : List Diagram → ℕ
  maxWidth  = foldr (λ d m → Diagram.width d ⊔ m) 0
  maxHeight = foldr (λ d m → Diagram.height d ⊔ m) 0

  resize : ℕ → ℕ → Diagram → Diagram
  resize w h d = record d { width = w ; height = h }

-- the `animation` command for an animation: `name-i` is the id of frame `i`
-- and `percent` the displayed width
render : (name : String) (percent : ℕ) → Anim ℕ (Seg ℕ) → ContentShape
render name pct a with compileFrames name pct 0 (timeline atop frames a)
... | []       = animation (compile (name ++ˢ "-0") pct (spacer 0 0)) []
... | d ∷ ds   = animation (resize w h d) (map (resize w h) ds)
  where w = maxWidth (d ∷ ds)
        h = maxHeight (d ∷ ds)
