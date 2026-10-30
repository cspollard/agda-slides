{-# OPTIONS --safe --without-K #-}

-- Writing a rational as a decimal: tick labels, and (later) the coordinates of a `Dia ℚ`.
--
-- `decimals d q` rounds to `d` places (half up, on the magnitude) and always shows them;
-- `trimmed d q` drops trailing zeros and a bare point, so a tick at 2.50 reads `2.5` and at 3.00
-- reads `3`.  A negative value that rounds to zero is written without a sign.

module Slides.Plot.Format where

open import Data.Bool using (not; if_then_else_; _∧_)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.List using (List; []; _∷_; _++_; length; replicate; reverse; dropWhileᵇ)
open import Data.Nat using (ℕ; zero; suc; _*_; _∸_; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ; ½; ∣_∣; _≤ᵇ_)
open import Data.String using (String; fromList; toList) renaming (_++_ to _++ˢ_)

open import Slides.Scalar.Model.Rat using (ι; ratFloor)

private
  pow10 : ℕ → ℕ
  pow10 zero    = 1
  pow10 (suc d) = 10 * pow10 d

  -- the digits of `n` with at least `d + 1` of them
  padded : ℕ → ℕ → List Char
  padded d n = replicate (suc d ∸ length ds) '0' ++ ds
    where ds = toList (show n)

  -- split off the last `d` digits
  split : ℕ → List Char → List Char × List Char
  split d cs = go (length cs ∸ d) cs
    where go : ℕ → List Char → List Char × List Char
          go zero    r        = [] , r
          go (suc k) []       = [] , []
          go (suc k) (c ∷ r)  = let p = go k r in c ∷ proj₁ p , proj₂ p

  -- round half up, on the magnitude, to `d` places, as a whole number of 10⁻ᵈ
  scaled : ℕ → ℚ → ℕ
  scaled d q = ratFloor (∣ q ∣ ℚ.* ι (pow10 d) ℚ.+ ½)

decimals : ℕ → ℚ → String
decimals d q = (if neg then "−" else "") ++ˢ fromList (proj₁ sp) ++ˢ (if d ≡ᵇ 0 then "" else "." ++ˢ fromList (proj₂ sp))
  where
    n   = scaled d q
    neg = (q ≤ᵇ 0ℚ) ∧ not (n ≡ᵇ 0)
    sp  = split d (padded d n)

trimmed : ℕ → ℚ → String
trimmed zero    q = decimals 0 q
trimmed (suc d) q = fromList (strip (toList (decimals (suc d) q)))
  where
    -- `dropWhile` on the reversed text removes trailing zeros; a point left at the end goes too
    stripPoint : List Char → List Char
    stripPoint ('.' ∷ r) = r
    stripPoint r         = r
    strip : List Char → List Char
    strip cs = reverse (stripPoint (dropWhileᵇ (λ c → c ≈ᵇ '0') (reverse cs)))

-- closed checks
private
  open import Data.Integer using (+_; -[1+_])
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  _ : decimals 2 (+ 5 ℚ./ 4) ≡ "1.25"
  _ = refl
  _ : decimals 1 (-[1+ 2 ] ℚ./ 2) ≡ "−1.5"
  _ = refl
  _ : decimals 2 (+ 1 ℚ./ 20) ≡ "0.05"
  _ = refl
  _ : decimals 0 (+ 7 ℚ./ 2) ≡ "4"
  _ = refl
  _ : trimmed 2 (+ 5 ℚ./ 2) ≡ "2.5"
  _ = refl
  _ : trimmed 2 (+ 3 ℚ./ 1) ≡ "3"
  _ = refl
  _ : trimmed 2 (-[1+ 0 ] ℚ./ 1000) ≡ "0"
  _ = refl
