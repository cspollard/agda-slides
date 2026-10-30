{-# OPTIONS --safe --without-K #-}

-- The looping background of the Pairs deck: dot pairs that turn (8 directions per half turn, one
-- step every 3 ticks) and sway (triangle wave) over a 64-tick period, so the last frame meets the first.
-- Pairs come from a seeded LCG, so output is reproducible.  The diagram is over scalar terms in
-- `now` (sway: a term; turning: a balanced comparison tree), so the page evaluates it per tick and
-- no frame is stored.  Pairs sit on canvas-sized layers (`place`, `overlay`): layout is linear in
-- the number of pairs.

module Slides.Examples.PairsHero where

open import Data.Bool.Base using (Bool; if_then_else_; true; false)
open import Data.Bool.ListAction using (all)
open import Data.List.Base using (List; []; _∷_; zipWith; upTo; foldr; map; length; splitAt; take; drop; lookup)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _∸_; _%_; _/_; _<ᵇ_; _≡ᵇ_; NonZero)
open import Data.Nat.Show using (show)
open import Data.Product.Base using (_×_; _,_)
open import Data.String.Base using (String) renaming (_++_ to _++ˢ_)
open import Data.Rational using (ℚ) renaming (_/_ to _÷_)
import Data.Rational.Properties as ℚP
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Integer using (ℤ; +_)
import Data.Integer as ℤ

open import Slides.Deck.Anim
open import Slides.Diagram.Syntax using (disc; named; connect; spacer; place; overlay)
open import Slides.Diagram.Geometry using (east; west)

W H period : ℕ
W = 1280
H = 720
period = 64

------------------------------------------------------------------------
-- The pairs

-- a pair: centre, radius, starting direction (of 8 over a half turn), spin (0, 1, 2 for -1, 0, 1
-- steps), sway amplitude and direction, and a colour
record Pair : Set where
  field
    cx cy radius angle spin amp : ℕ
    swayX swayY blue : Bool

-- the next pseudo-random number
next : ℕ → ℕ
next s = (s * 1103515245 + 12345) % 2147483648

-- `k` pairs from a seed
pairs : ℕ → ℕ → List Pair
pairs zero    s = []
pairs (suc k) s = p ∷ pairs k s₉
  where
    s₁ = next s; s₂ = next s₁; s₃ = next s₂; s₄ = next s₃; s₅ = next s₄
    s₆ = next s₅; s₇ = next s₆; s₈ = next s₇; s₉ = next s₈
    pick : ℕ → ℕ → (n : ℕ) → {{_ : NonZero n}} → ℕ
    pick seed lo n = lo + (seed / 65536) % n
    p = record
      { cx = pick s₁ 130 1020; cy = pick s₂ 110 500; radius = pick s₃ 26 60
      ; angle = pick s₄ 0 8; spin = pick s₅ 0 3; amp = pick s₆ 20 36
      ; swayX = pick s₇ 0 2 <ᵇ 1; swayY = pick s₈ 0 2 <ᵇ 1; blue = pick s₉ 0 2 <ᵇ 1 }

------------------------------------------------------------------------
-- Terms in the tick

-- the cosine and sine of direction `i` of 8, in hundredths (the lines through it rise to the right
-- for the directions 5, 6, 7, so that "left" is the lower end)
tabX tabY : List ℕ
tabX = 100 ∷ 92 ∷ 71 ∷ 38 ∷ 0 ∷ 38 ∷ 71 ∷ 92 ∷ []
tabY = 0 ∷ 38 ∷ 71 ∷ 92 ∷ 100 ∷ 92 ∷ 71 ∷ 38 ∷ []

at : List ℕ → ℕ → ℕ
at []       _       = 0
at (x ∷ _)  zero    = x
at (_ ∷ xs) (suc i) = at xs i

-- the direction in phase `k` (a phase is three ticks): turning one step every phase, modulo 7
direction : Pair → ℕ → ℕ
direction p k = (Pair.angle p + spin′) % 7
  where
    q = k % 7
    spin′ = if Pair.spin p <ᵇ 1 then 8 ∸ q else if Pair.spin p <ᵇ 2 then 0 else q

-- the phases of a period (a phase is three ticks; the last one is cut short)
phases : ℕ
phases = 22

-- a step function of the tick from its values on the phases `0, 1, …`: a balanced tree of
-- comparisons, a constant when every phase has the same value
stepFn : List ℚ → Sc
stepFn []         = lit 0
stepFn vs@(v ∷ r) = if all (λ w → ⌊ v ℚP.≟ w ⌋) r then litQ v else go (length vs) 0 vs
  where
    -- `lo` is the first phase of `xs`; the fuel is its length
    go : ℕ → ℕ → List ℚ → Sc
    go zero    lo xs       = lit 0
    go (suc f) lo []       = lit 0
    go (suc f) lo (x ∷ []) = litQ x
    go (suc f) lo xs@(_ ∷ _ ∷ _) =
      ifle (lit (3 * (lo + m))) now (go f (lo + m) (drop m xs)) (go f lo (take m xs))
      where m = length xs / 2

------------------------------------------------------------------------
-- One pair at the tick `now`

-- a dot of radius `r` with its top left corner at (x, y), on a layer of the canvas's size
dot : String → String → ℕ → Sc → Sc → Leaf
dot name cls r x y =
  place (lit W) (lit H) x y (named name (disc (lit r) (withClass cls defaultStyle)))

hundredths : ℤ → ℚ
hundredths z = z ÷ 100

pairAt : ℕ → Pair → Leaf
pairAt i p = connect ("a" ++ˢ si) east ("b" ++ˢ si) west (withClass "hero-link" defaultStyle)
               (overlay (lit W) (lit H)
                  (dot ("a" ++ˢ si) col 5 (ox ⊟ ddx ⊟ lit 5) (oy ⊞ ddy ⊟ lit 5))
                  (dot ("b" ++ˢ si) col 5 (ox ⊞ ddx ⊟ lit 5) (oy ⊟ ddy ⊟ lit 5)))
  where
    open Pair p
    si  = show i
    col = if blue then "hero-b" else "hero-r"
    -- the triangle wave 0 … 32 … 0 of the tick, scaled to the amplitude: `amp * tri / 32`
    tri = ifle now (lit 32) now (lit 64 ⊟ now)
    d   = pctOf ((amp * 100 + 16) / 32) tri
    ox  = lit (cx ∸ amp) ⊞ (if swayX then d else lit amp ⊟ d)
    oy  = lit (cy ∸ amp) ⊞ (if swayY then d else lit amp ⊟ d)
    -- half the pair's extent along x, and y of the left dot relative to the centre
    dirs = map (direction p) (upTo phases)
    ddx = stepFn (map (λ a → hundredths (+ (radius * at tabX a))) dirs)
    ddy = stepFn (map (λ a → hundredths ((if a <ᵇ 5 then ℤ.-_ else (λ z → z)) (+ (radius * at tabY a)))) dirs)

-- the whole picture: every pair on a layer of the canvas's size, the layers overlaid
heroFrame : (n seed : ℕ) → Leaf
heroFrame n seed = foldr (overlay (lit W) (lit H)) (spacer (lit W) (lit H)) (zipWith pairAt (upTo n) (pairs n seed))

-- one period, played as a loop (`animateLoop`): the tick runs from 0 to the period
heroLoop : (n seed : ℕ) → Anim
heroLoop n seed = tween Linear (ι 0) (ι period) (ι period) (heroFrame n seed)
