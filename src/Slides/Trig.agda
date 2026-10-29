{-# OPTIONS --safe --without-K #-}

-- Sine and cosine of an angle in rational turns, exactly folded and then approximated.
--
-- The circle is folded by exact symmetries, which cost nothing in ℚ: a whole number of quarter
-- turns is a rotation of the pair (cos , sin) (`quarter`), and the rest of a quarter is folded about
-- its middle (sin (¼ − v) = cos v).  What is left is an angle of at most an eighth of a turn,
-- where the Taylor polynomial of order `n` in Horner form is accurate to (π/4)ⁿ⁺¹/(n+1)!: about
-- 3·10⁻⁴ for n = 5 and 10⁻⁸ for n = 9.  Turns are converted to radians by `tau`, a convergent of 2π
-- (a parameter: any other works).  No tables, no floating point.

module Slides.Trig where

open import Data.Integer using (ℤ; +_; _%ℕ_)
open import Data.Nat using (ℕ; zero; suc; _∸_; _/_) renaming (_*_ to _·_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; swap)
open import Data.Bool using (if_then_else_)
open import Data.Rational.Unnormalised using (ℚᵘ; mkℚᵘ; 1ℚᵘ; floor; _+_; _-_; _*_; -_; _≤ᵇ_)

-- a whole number as a rational
fromℕ : ℕ → ℚᵘ
fromℕ m = mkℚᵘ (+ m) 0

-- 1 − t/(m(m+1)) (1 − t/((m+2)(m+3)) (…)), `k` factors: Horner form of the alternating series
-- (cos at m = 1, sin / θ at m = 2, with t = θ²)
tail : ℕ → ℕ → ℚᵘ → ℚᵘ
tail zero    _ _ = 1ℚᵘ
tail (suc k) m t = 1ℚᵘ - (t * mkℚᵘ (+ 1) (m · suc m ∸ 1)) * tail k (suc (suc m)) t

-- 2π, as the convergent 710/113
tau : ℚᵘ
tau = mkℚᵘ (+ 710) 112

-- (cos , sin) of x turns, 0 ≤ x ≤ 1/8
eighth : ℕ → ℚᵘ → ℚᵘ × ℚᵘ
eighth n x = tail (n / 2) 1 t , θ * tail (n / 2) 2 t
  where θ = tau * x
        t = θ * θ

-- … and 0 ≤ x ≤ 1/4: the far half is the near half seen from the other end
fold : ℕ → ℚᵘ → ℚᵘ × ℚᵘ
fold n x = if x ≤ᵇ mkℚᵘ (+ 1) 7
  then eighth n x
  else swap (eighth n (mkℚᵘ (+ 1) 3 - x))

-- (cos , sin) of q quarter turns more
quarter : ℕ → ℚᵘ × ℚᵘ → ℚᵘ × ℚᵘ
quarter 0 (c , s) = c , s
quarter 1 (c , s) = - s , c
quarter 2 (c , s) = - c , - s
quarter _ (c , s) = s , - c

-- (cos , sin) of x turns, by polynomials of order n
cis : ℕ → ℚᵘ → ℚᵘ × ℚᵘ
cis n x = quarter (k %ℕ 4) (fold n (x - mkℚᵘ k 3))
  where k = floor (mkℚᵘ (+ 4) 0 * x)

sin cos : ℕ → ℚᵘ → ℚᵘ
sin n x = proj₂ (cis n x)
cos n x = proj₁ (cis n x)

-- the whole number nearest to a rational (0 for a negative one): where a number leaves ℚ
nearest : ℚᵘ → ℕ
nearest v = clamp (floor (v + mkℚᵘ (+ 1) 1))
  where clamp : ℤ → ℕ
        clamp (+ m) = m
        clamp _     = 0

-- the whole number nearest to c + d u
shift : ℕ → ℕ → ℚᵘ → ℕ
shift c d u = nearest (fromℕ c + fromℕ d * u)
