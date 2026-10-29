{-# OPTIONS --safe --without-K #-}

-- Sine and cosine of an angle in 1/1024 turns, in whole numbers: a 17-entry table of the first
-- quadrant, linearly interpolated (under 0.2 % off).

module Slides.Trig where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Integer using (ℤ; +_) renaming (-_ to negᶻ)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _/_; _%_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

-- sin of 0, 5.625°, … 90°, then 90° again so that interpolation at the end has a neighbour
sinTable : List ℕ
sinTable = 0 ∷ 980 ∷ 1951 ∷ 2903 ∷ 3827 ∷ 4714 ∷ 5556 ∷ 6344 ∷ 7071
         ∷ 7730 ∷ 8315 ∷ 8819 ∷ 9239 ∷ 9569 ∷ 9808 ∷ 9952 ∷ 10000 ∷ 10000 ∷ []

nth : ℕ → List ℕ → ℕ
nth _       []       = 0
nth zero    (x ∷ _)  = x
nth (suc k) (_ ∷ xs) = nth k xs

-- sin of a first-quadrant angle (a ≤ 256), interpolated between the table entries
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
