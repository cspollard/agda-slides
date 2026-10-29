{-# OPTIONS --safe --without-K #-}

-- Looking at a `Point`: a `View` turns space about the vertical axis (`yaw`, which shows the
-- length of a cylinder) and about the line of sight (`roll`, which tilts the picture); `project` is
-- the point on the page, in orthographic projection, about a given centre.
--
-- A turn is the pair (cos , sin) of its angle.  It comes from an angle in turns (`viewA`, by the
-- polynomials of `Slides.Trig`), or from a rational tangent of the half angle (`viewT`): t gives
-- (1 − t² , 2t) / (1 + t²), exactly a unit vector, so these turns need no trig and compose
-- without error.

module Slides.Three.View where

open import Data.Integer as ℤ using (ℤ; +_)
open import Data.Nat as ℕ using (ℕ; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (ℚᵘ; mkℚᵘ; 0ℚᵘ; _+_; _-_; _*_)

open import Slides.Trig using (cis; fromℕ; nearest)
open import Slides.Three.Point

-- the turn (c , s) acting on the pair (x , y)
act : ℚᵘ × ℚᵘ → ℚᵘ × ℚᵘ → ℚᵘ × ℚᵘ
act (c , s) (x , y) = c * x - s * y , s * x + c * y

-- the turn whose half angle has tangent t
tangent : ℚᵘ → ℚᵘ × ℚᵘ
tangent (mkℚᵘ p q) = mkℚᵘ (+ (suc q ℕ.* suc q) ℤ.- + p²) m , mkℚᵘ (+ 2 ℤ.* p ℤ.* + suc q) m
  where p² = ℤ.∣ p ∣ ℕ.* ℤ.∣ p ∣
        m  = q ℕ.+ q ℕ.* suc q ℕ.+ p²

record View : Set where
  constructor view
  field
    yaw roll : ℚᵘ × ℚᵘ

-- two angles in turns (polynomials of order n), and two tangents of half angles
viewA : ℕ → ℚᵘ → ℚᵘ → View
viewA n a b = view (cis n a) (cis n b)

viewT : ℚᵘ → ℚᵘ → View
viewT t u = view (tangent t) (tangent u)

-- looking down the axis, and a little turned (14° and 3°) to show the length
flat turned : View
flat   = viewT 0ℚᵘ 0ℚᵘ
turned = viewT (mkℚᵘ (+ 37) 299) (mkℚᵘ (+ 4) 162)

rotate : View → Point → Point
rotate (view yw rl) (point x y z) = point (proj₁ b) (proj₂ b) (proj₂ a)
  where a = act yw (x , z)
        b = act rl (proj₁ a , y)

-- the point of the page, about the centre (cx , cy), under a turned point; and under a view.  The
-- far end (z negative) moves to the right, so the outer surface of a cylinder shows on the right.
screen : ℕ → ℕ → Point → ℕ × ℕ
screen cx cy p = nearest (fromℕ cx + Point.x p) , nearest (fromℕ cy + Point.y p)

project : ℕ → ℕ → View → Point → ℕ × ℕ
project cx cy V p = screen cx cy (rotate V p)
