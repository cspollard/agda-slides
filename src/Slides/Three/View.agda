{-# OPTIONS --safe --without-K #-}

-- Looking at a `Point`: a `View` turns space about the vertical axis (`yaw`, which shows the
-- length of a cylinder) and about the line of sight (`roll`, which tilts the picture), in 1/1024
-- turns; `project` is the point on the page, in orthographic projection, about a given centre.
-- The view `flat` looks down the axis.

module Slides.Three.View where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Integer using (ℤ; +_) renaming (_+_ to _+ᶻ_; _*_ to _*ᶻ_; _-_ to _-ᶻ_; -_ to negᶻ; ∣_∣ to absᶻ)
open import Data.Nat using (ℕ; suc; _+_; _*_; _∸_; _/_; _%_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Slides.Examples.LHC using (sinTable; nth)
open import Slides.Three.Point

------------------------------------------------------------------------
-- Trigonometry: angles in 1/1024 turns

-- sin of a first-quadrant angle (a ≤ 256), interpolated between the 17 table entries
sinQ : ℕ → ℕ
sinQ a = lo + ((hi ∸ lo) * (a % 16)) / 16
  where lo = nth (a / 16) sinTable
        hi = nth (suc (a / 16)) sinTable

-- (cos , sin) as a magnitude in tenthousandths and a flag that it is negative
trig : ℕ → (ℕ × Bool) × (ℕ × Bool)
trig a = quad ((a / 256) % 4) (a % 256)
  where
    quad : ℕ → ℕ → (ℕ × Bool) × (ℕ × Bool)
    quad 0 r = (sinQ (256 ∸ r) , false) , (sinQ r , false)
    quad 1 r = (sinQ r , true)          , (sinQ (256 ∸ r) , false)
    quad 2 r = (sinQ (256 ∸ r) , true)  , (sinQ r , true)
    quad _ r = (sinQ r , false)         , (sinQ (256 ∸ r) , true)

-- (cos , sin) in tenthousandths
sc : ℕ → ℤ × ℤ
sc a = signed (proj₁ t) , signed (proj₂ t)
  where t = trig a
        signed : ℕ × Bool → ℤ
        signed (m , neg) = if neg then negᶻ (+ m) else + m

------------------------------------------------------------------------
-- Views

record View : Set where
  constructor view
  field
    yaw roll : ℕ

-- looking down the axis, and a little turned (14° and 3°) to show the length
flat turned : View
flat   = view 0 0
turned = view 40 8

-- the point on the page, about the centre (cx , cy).  The far end (z negative) moves to the right,
-- so the outer surface of a cylinder shows on the right.
project : ℕ → ℕ → View → Point → ℕ × ℕ
project cx cy (view yw rl) (cyl r a z) = fin cx x₂ , fin cy y₂
  where
    c  s  cθ sθ cρ sρ : ℤ
    c  = proj₁ (sc a)
    s  = proj₂ (sc a)
    cθ = proj₁ (sc yw)
    sθ = proj₂ (sc yw)
    cρ = proj₁ (sc rl)
    sρ = proj₂ (sc rl)

    -- the turn about the vertical axis (scaled 10⁸), then the roll (10¹²)
    x₁ y₁ x₂ y₂ : ℤ
    x₁ = (((+ r) *ᶻ c) *ᶻ cθ) -ᶻ ((z *ᶻ + 100) *ᶻ sθ)
    y₁ = ((+ r) *ᶻ s) *ᶻ + 10000
    x₂ = (x₁ *ᶻ cρ) -ᶻ (y₁ *ᶻ sρ)
    y₂ = (x₁ *ᶻ sρ) +ᶻ (y₁ *ᶻ cρ)

    scale : ℕ
    scale = 1000000000000

    -- the centre moved by the scaled offset, to the nearest unit (the offset keeps it positive)
    fin : ℕ → ℤ → ℕ
    fin c₀ v = (absᶻ (v +ᶻ + ((c₀ + 2000) * scale + scale / 2)) / scale) ∸ 2000

-- how far towards the viewer a point is, to compare: the turn about the vertical axis takes its x
-- to a depth of x times the sine of the yaw
depth : View → Point → ℤ
depth (view yw _) (cyl r a z) = (((+ r) *ᶻ proj₁ (sc a)) *ᶻ proj₂ (sc yw)) +ᶻ ((z *ᶻ + 100) *ᶻ proj₁ (sc yw))
