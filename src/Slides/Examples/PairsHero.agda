{-# OPTIONS --safe --without-K #-}

-- The drifting point pairs behind the title and closing slides of the Pairs deck,
-- as a loop (`Slides.Anim.Loop`): each pair is two dots joined by a line; over one
-- period of `period` frames a pair turns through a half turn (the pair is unordered)
-- and sways to and fro along a fixed direction, a triangle wave, so the last frame
-- runs into the first and nothing jumps.  The pairs are a deterministic function of
-- a seed (a linear congruential generator), so the output is reproducible.

module Slides.Examples.PairsHero where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; map; zipWith; upTo; foldr)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _%_; _/_; _<ᵇ_; NonZero)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Integer using (+_)
import Data.Rational as ℚ

open import Slides.Diagram using (Style; withClass; defaultStyle)
open import Slides.Diagram.Syntax using (Dia; disc; atop; named; connect; spacer)
open import Slides.Diagram.Notation using (margin; side; east; west)
open import Slides.Anim.Syntax using (Anim; Seg; tween; units)
import Slides.Anim.Track as T

W H period : ℕ
W = 1280
H = 720
period = 64

------------------------------------------------------------------------
-- The pairs

-- a pair: centre, radius, starting angle (of 8 over a half turn), spin (-1, 0, 1 as 0, 1, 2),
-- sway amplitude and direction, and a colour
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
-- A frame

-- the direction of angle `i` of 8: |dx|, |dy| in hundredths, and whether the line
-- through it rises to the right (so that "left" is the lower end)
dir : ℕ → ℕ × ℕ × Bool
dir 0 = 100 , 0   , false
dir 1 = 92  , 38  , false
dir 2 = 71  , 71  , false
dir 3 = 38  , 92  , false
dir 4 = 0   , 100 , false
dir 5 = 38  , 92  , true
dir 6 = 71  , 71  , true
dir _ = 92  , 38  , true

-- the triangle wave: 0 up to 32 and back down over a period
tri : ℕ → ℕ
tri t = let m = t % period in if m <ᵇ 33 then m else period ∸ m

-- a dot of radius `r` with its top left corner at (x, y), on a full-size layer
dot : String → String → ℕ → ℕ → ℕ → Dia ℕ
dot name cls r x y =
  margin x y (W ∸ (x + 2 * r)) (H ∸ (y + 2 * r))
    (named name (disc r (withClass cls defaultStyle)))

-- one pair at frame `t`
pairAt : ℕ → ℕ → Pair → Dia ℕ
pairAt t i p = connect ("a" ++ˢ si) east ("b" ++ˢ si) west (withClass "hero-link" defaultStyle)
                 (atop (dot ("a" ++ˢ si) col 5 (lx ∸ 5) (ly ∸ 5)) (dot ("b" ++ˢ si) col 5 (rx ∸ 5) (ry ∸ 5)))
  where
    open Pair p
    si  = show i
    col = if blue then "hero-b" else "hero-r"
    -- the angle turns by `spin - 1` steps every four frames
    ang = (angle + (if spin <ᵇ 1 then 8 ∸ (t / 4) % 8 else if spin <ᵇ 2 then 0 else (t / 4) % 8)) % 8
    dxʰ = let (a , _ , _) = dir ang in a
    dyʰ = let (_ , b , _) = dir ang in b
    rising = let (_ , _ , r) = dir ang in r
    dx = (radius * dxʰ) / 100
    dy = (radius * dyʰ) / 100
    -- the sway: along x and y by `amp * tri t / 32`
    d  = (amp * tri t) / 32
    ox = cx ∸ amp + (if swayX then d else amp ∸ d)
    oy = cy ∸ amp + (if swayY then d else amp ∸ d)
    lx = ox ∸ dx
    rx = ox + dx
    ly = if rising then oy + dy else oy ∸ dy
    ry = if rising then oy ∸ dy else oy + dy

-- the whole picture at frame `t`: every pair on a layer of the canvas's size
heroAt : (seed : ℕ) → ℕ → Dia ℕ
heroAt seed t = foldr atop (spacer W H) (zipWith (pairAt t) (upTo 26) (pairs 26 seed))

-- one period of the sway and spin, played as a loop
hero : ℕ → Anim ℕ (Seg ℕ)
hero seed = tween period (+ 0 ℚ./ 1) (+ period ℚ./ 1) T.Linear (λ q → heroAt seed (units q))
