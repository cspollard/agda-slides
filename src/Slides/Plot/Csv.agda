{-# OPTIONS --safe --without-K #-}

-- Data in.  Nothing in the core does IO: an executable reads the file (`Slides.Examples.PlotsDataMain`)
-- and hands the text to these pure functions, which give the numbers as ℚ, exactly (`1.25` is 5/4,
-- no floating point).
--
-- A line is fields separated by commas; a number is an optional sign, digits, and an optional
-- fraction (spaces are ignored).  A line with a field that is not a number (a header, a comment)
-- is skipped, as are blank lines.  Exponents are not read.

module Slides.Plot.Csv where

open import Data.Bool using (Bool; true; false; not; _∨_; _∧_; if_then_else_)
open import Data.Char using (Char; _≟_)
open import Data.Sign as Sign using (Sign)
open import Data.Integer as ℤ using (ℤ; +_; -_)
open import Data.List using (List; []; _∷_; map; length; wordsByᵇ; filter; mapMaybe; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat as ℕ using (ℕ)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ)
open import Data.String using (String; toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (does)

open import Data.CSS.Number using (CSSNumber; cssNumber; lexNumber)
open import Data.Number.Digits using (digitsToNat)
open import Slides.Plot.Data using (decimal)
open import Slides.Scalar.Model.Rat using (ι)

private
  is : Char → Char → Bool
  is a b = does (a ≟ b)

  -- the lexer of `parsnip` reads `digits [. digits]` (no exponent) as sign, integral, fraction digits
  value : CSSNumber → ℚ
  value (cssNumber sg i f) = signed sg (decimal (+ (i ℕ.* 10 ℕ.^ k ℕ.+ digitsToNat f)) k)
    where k = length f
          signed : Sign → ℚ → ℚ
          signed Sign.+ q = q
          signed Sign.- q = ℚ.- q

  whole : Sign → List Char → Maybe ℚ
  whole sg cs with lexNumber sg cs
  ... | just (n , []) = just (value n)
  ... | _             = nothing

  -- a whole field is one number
  signed : List Char → Maybe ℚ
  signed ('-' ∷ cs) = whole Sign.- cs
  signed ('+' ∷ cs) = whole Sign.+ cs
  signed cs         = whole Sign.+ cs

  number : List Char → Maybe ℚ
  number cs = signed (filterᵇ (λ c → not (is c ' ')) cs)

  row : List (List Char) → Maybe (List ℚ)
  row []       = just []
  row (f ∷ fs) with number f | row fs
  ... | just q | just qs = just (q ∷ qs)
  ... | _      | _       = nothing

-- the rows of numbers in a text (lines that are not all numbers are skipped)
rows : String → List (List ℚ)
rows s = mapMaybe (λ l → row (wordsByᵇ (is ',') l)) (wordsByᵇ (λ c → is c '\n' ∨ is c '\r') (toList s))

-- the first two columns as points, and the first three
xy : List (List ℚ) → List (ℚ × ℚ)
xy = mapMaybe λ { (x ∷ y ∷ _) → just (x , y) ; _ → nothing }

xye : List (List ℚ) → List (ℚ × ℚ × ℚ)
xye = mapMaybe λ { (x ∷ y ∷ e ∷ _) → just (x , y , e) ; _ → nothing }

private
  _ : rows "x,y\n1,2.5\n-3, 0.25\n\n" ≡ (ι 1 ∷ decimal (+ 25) 1 ∷ []) ∷ (ℚ.- ι 3 ∷ decimal (+ 25) 2 ∷ []) ∷ []
  _ = refl
