{-# OPTIONS --safe --without-K #-}

-- Logarithmic axes: a value is plotted at `log₁₀` of it, on the ordinary linear axis.
--
-- No reals and no `Float`, so `log₁₀` is computed in ℚ: shift by powers of ten into [0.316, 3.16),
-- add the shift, then ln m = 2 (z + z³/3 + … + z⁹/9) with z = (m − 1)/(m + 1) (|z| < 0.52, an error
-- under 10⁻³ decades, far below a pixel) times 1/ln 10.  Exact where it matters: `log₁₀ 10ᵏ = k`
-- (m = 1, z = 0), so decade ticks and their labels are exact.  The approximation is checked on
-- closed values below; monotonicity of the polynomial is not proved.
--
-- `logMark` maps a mark into log space.  An error bar keeps its end points exact: its centre is the
-- middle of the logs of its ends, so the dot (a separate scatter) and the bar's middle differ.

module Slides.Plot.Log where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_])
open import Data.List using (List; map)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤ᵇ_; -_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Slides.Plot.Data using (inv; decimal)
open import Slides.Plot.Mark
open import Slides.Scalar.Model.Rat using (ι)

private
  lt : ℚ → ℚ → Bool
  lt a b = if b ≤ᵇ a then false else true

  -- the mantissa in [0.316, 3.16) and the power of ten shifted out (the fuel bounds the shifts)
  norm : ℕ → ℚ → ℤ → ℚ × ℤ
  norm zero    m k = m , k
  norm (suc n) m k =
    if decimal (+ 316) 2 ≤ᵇ m then norm n (m * decimal (+ 1) 1) (k ℤ.+ + 1)
    else if lt m (decimal (+ 316) 3) then norm n (m * ι 10) (k ℤ.+ -[1+ 0 ])
    else (m , k)

  -- z + z³/3 + z⁵/5 + …, `n` terms, from the power `p` and odd number `o`
  atanh : ℕ → ℚ → ℚ → ℚ → ℚ
  atanh zero    _  _  _ = 0ℚ
  atanh (suc n) z2 p o  = p * inv o + atanh n z2 (p * z2) (o + ι 2)

-- log₁₀ of a positive number; −20 for the others (off the bottom of any sensible axis)
log10 : ℚ → ℚ
log10 x = if lt 0ℚ x then go (norm 40 x (+ 0)) else - ι 20
  where
    go : ℚ × ℤ → ℚ
    go (m , k) = (k ℚ./ 1) + ι 2 * decimal (+ 4342944819) 10 * atanh 5 (z * z) z 1ℚ
      where z = (m - 1ℚ) * inv (m + 1ℚ)

-- 10ᵏ
tenPow : ℤ → ℚ
tenPow (+ n)    = ι (p n)
  where p : ℕ → ℕ
        p zero = 1
        p (suc k) = 10 ℕ.* p k
tenPow -[1+ n ] = inv (tenPow (+ suc n))

logMark : Mark → Mark
logMark (line s ps)     = line s (map (λ { (x , y) → x , log10 y }) ps)
logMark (scatter s ps)  = scatter s (map (λ { (x , y) → x , log10 y }) ps)
logMark (steps s es hs) = steps s es (map log10 hs)
logMark (band s ts)     = band s (map (λ { (x , l , h) → x , log10 l , log10 h }) ts)
logMark (errors s ts)   = errors s (map (λ { (x , y , e) →
                            let l = log10 (y - e) ; h = log10 (y + e)
                            in x , (l + h) * decimal (+ 5) 1 , (h - l) * decimal (+ 5) 1 }) ts)
logMark (hline s y)     = hline s (log10 y)
logMark (vline s x)     = vline s x
logMark (note x y t)    = note x (log10 y) t

private
  near : ℚ → ℚ → Bool
  near a b = ((a - b) ≤ᵇ decimal (+ 1) 3) ∧ ((b - a) ≤ᵇ decimal (+ 1) 3)

  _ : (log10 (ι 1) ≡ 0ℚ) × (log10 (ι 100) ≡ ι 2) × (log10 (decimal (+ 1) 1) ≡ - ι 1)
  _ = refl , refl , refl

  _ : near (log10 (ι 2)) (decimal (+ 30103) 5) ≡ true
  _ = refl
  _ : near (log10 (ι 3)) (decimal (+ 47712) 5) ≡ true
  _ = refl
  _ : near (log10 (ι 5)) (decimal (+ 69897) 5) ≡ true
  _ = refl
  _ : near (log10 (ι 7)) (decimal (+ 84510) 5) ≡ true
  _ = refl
  _ : near (log10 (decimal (+ 3) 2)) (- ι 2 + decimal (+ 47712) 5) ≡ true
  _ = refl
