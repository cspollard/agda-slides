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

open import Data.List using (List; []; _∷_; map; foldr; concat; length; upTo)
open import Data.List.Properties using (≡-dec)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (True)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; _⊔_; _+_; _∸_; suc)
open import Data.Nat.Show using (show)
open import Data.String using (String) renaming (_++_ to _++ˢ_)

open import Slides.Core using (ContentShape; animation; Play; onSteps; looping; both)
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

-- the diagrams of the frames, all of one size: `name-i` is the id of frame `i`,
-- `percent` the displayed width.  A zero-length animation is one empty frame.
frameDiagrams : String → ℕ → List (Dia ℕ) → List Diagram
frameDiagrams name pct fs with compileFrames name pct 0 fs
... | []     = compile (name ++ˢ "-0") pct (spacer 0 0) ∷ []
... | d ∷ ds = map (resize w h) (d ∷ ds)
  where w = maxWidth (d ∷ ds)
        h = maxHeight (d ∷ ds)

-- the `animation` command for frames played in a given mode: `ms` is the time per frame
private
  shape : String → ℕ → ℕ → (Play) → List (Dia ℕ) → ContentShape
  shape name pct ms play fs with frameDiagrams name pct fs
  ... | []     = animation (compile (name ++ˢ "-0") pct (spacer 0 0)) [] ms play
  ... | d ∷ ds = animation d ds ms play

-- the acts one after the other; each act is one step
render : (name : String) (percent ms : ℕ) → List (Anim ℕ (Seg ℕ)) → ContentShape
render name pct ms acts =
  shape name pct ms (onSteps (restsOf 0 (map (λ a → length (timeline atop frames a)) acts)))
        (concat (map (timeline atop frames) acts))

-- one animation, repeating
renderLoop : (name : String) (percent ms : ℕ) → Anim ℕ (Seg ℕ) → ContentShape
renderLoop name pct ms a = shape name pct ms looping (timeline atop frames a)

-- Steps over a loop: `acts φ` are the acts at phase `φ` of a loop of `period` phases
-- (a phase typically only restyles the diagram: an arrow's dashes, a pulse).  Each
-- phase is a full copy of the steps, so every phase must have acts of the same
-- lengths; that is checked by computation (the instance argument is `⊤` when it
-- holds, and the deck does not typecheck when it does not).
private
  lengths : List (Anim ℕ (Seg ℕ)) → List ℕ
  lengths = map (λ a → length (timeline atop frames a))

Uniform : ℕ → (ℕ → List (Anim ℕ (Seg ℕ))) → Set
Uniform period acts = All (λ φ → lengths (acts φ) ≡ lengths (acts 0)) (upTo period)

uniform? : ∀ period acts → Dec (Uniform period acts)
uniform? period acts = All.all? (λ φ → ≡-dec _≟_ (lengths (acts φ)) (lengths (acts 0))) (upTo period)

renderBoth : (name : String) (percent ms period : ℕ) (acts : ℕ → List (Anim ℕ (Seg ℕ))) →
             {{_ : True (uniform? period acts)}} → ContentShape
renderBoth name pct ms period acts =
  shape name pct ms (both (restsOf 0 (lengths (acts 0))) period)
        (concat (map (λ φ → concat (map (timeline atop frames) (acts φ))) (upTo period)))
