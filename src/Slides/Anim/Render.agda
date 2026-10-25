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

open import Data.List using (List; []; _∷_; map; foldr; concat; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; _⊔_; _+_; _∸_; suc)
open import Data.Nat.Show using (show)
open import Data.String using (String) renaming (_++_ to _++ˢ_)

open import Slides.Core using (ContentShape; animation; Play; onSteps; looping)
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

-- the frame each act comes to rest on: act `j` ends at the total length so far
-- minus one (the last frame of the act)
restsOf : ℕ → List ℕ → List ℕ
restsOf acc []       = []
restsOf acc (l ∷ ls) = (acc + l ∸ 1) ∷ restsOf (acc + l) ls

length-restsOf : ∀ acc ls → length (restsOf acc ls) ≡ length ls
length-restsOf acc []       = refl
length-restsOf acc (l ∷ ls) = cong suc (length-restsOf (acc + l) ls)

-- the `animation` command for frames played in a given mode: `name-i` is the id of
-- frame `i`, `percent` the displayed width, `ms` the time per frame.  A zero-length
-- animation is one empty frame.
private
  shape : String → ℕ → ℕ → (Play) → List (Dia ℕ) → ContentShape
  shape name pct ms play fs with compileFrames name pct 0 fs
  ... | []     = animation (compile (name ++ˢ "-0") pct (spacer 0 0)) [] ms play
  ... | d ∷ ds = animation (resize w h d) (map (resize w h) ds) ms play
    where w = maxWidth (d ∷ ds)
          h = maxHeight (d ∷ ds)

-- the acts one after the other; each act is one step
render : (name : String) (percent ms : ℕ) → List (Anim ℕ (Seg ℕ)) → ContentShape
render name pct ms acts =
  shape name pct ms (onSteps (restsOf 0 (map (λ a → length (timeline atop frames a)) acts)))
        (concat (map (timeline atop frames) acts))

-- one animation, repeating
renderLoop : (name : String) (percent ms : ℕ) → Anim ℕ (Seg ℕ) → ContentShape
renderLoop name pct ms a = shape name pct ms looping (timeline atop frames a)
