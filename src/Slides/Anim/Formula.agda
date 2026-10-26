{-# OPTIONS --safe --without-K #-}

-- The formulas shipped to the page.
--
-- A template's symbolic layout has a formula (`Slides.Diagram.Expr`) at every coordinate.  The
-- backend ships it as a small tree the page evaluates in real numbers (`ev` in
-- `assets/animation.js`): a number, the parameter of a segment, `+`, `-` (real subtraction),
-- `m` (maximum), `["%", p, a]` ("p percent of a") and `["h", a]` (half of `a`, positions being
-- in half units).  Closed subformulas are folded when the result is exact: a closed
-- difference when the minuend is at least the subtrahend, a closed percentage when it divides
-- evenly, a half when the number is even.  Sums and maxima of closed formulas always fold
-- (`enc`).
--
-- Discrete templates (`Slides.Diagram.Euclid`) are read in ℕ, so there a closed node always folds,
-- whatever its operation (`encD`).
--
-- This module is the data and the encoders, which is what the backend runs; what they mean
-- (the readings `⟦_⟧` in ℚ, `⟦_⟧ᴺ`, `⟦_⟧ᴰ` in ℕ and the proofs that the folds are exact) is
-- `Slides.Anim.FormulaCorrect`.

module Slides.Anim.Formula where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (zero) renaming (suc to fsuc)
open import Data.Container.FreeMonad using (pure; impure)
open import Data.Nat as ℕ using (ℕ; suc; _*_; _/_; _%_; _≤ᵇ_; _<ᵇ_; _∸_; _+_; _⊔_; _≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (tt)
open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary.Decidable using (⌊_⌋)
import Data.Product.Properties as ΣP
import Data.Nat.Properties as ℕP

open import Slides.Diagram.Expr using (Expr)
import Slides.Diagram.Expr as E
open import Slides.Diagram.Euclid using (DExpr)
import Slides.Diagram.Euclid as Eu
open import Slides.DecEq

data Formula : Set where
  num  : ℕ → Formula                 -- a whole number
  var  : ℕ → Formula                 -- the parameter of a segment
  add sub max : Formula → Formula → Formula
  pct  : ℕ → Formula → Formula       -- `p` percent of
  hlf  : Formula → Formula           -- half of
  -- the Euclidean layer (`Slides.Diagram.Euclid`; discrete templates only, read in ℕ)
  fdiv fmod : ℕ → Formula → Formula  -- `fdiv d a`: a / (d+1), `fmod d a`: a % (d+1)
  fmul : ℕ → Formula → Formula       -- a literal factor
  flt  : Formula → Formula → Formula → Formula → Formula   -- `flt a b x y`: x if a < b else y


isNum : Formula → Bool
isNum (num _) = true
isNum _       = false

------------------------------------------------------------------------
-- Folding closed subformulas, when exact

plus : Formula → Formula → Formula
plus (num a) (num b) = num (a + b)
plus a       b       = add a b

-- a closed difference is folded when it is not negative
monus : Formula → Formula → Formula
monus (num a) (num b) = if b ≤ᵇ a then num (a ∸ b) else sub (num a) (num b)
monus a       b       = sub a b

maxF : Formula → Formula → Formula
maxF (num a) (num b) = num (a ⊔ b)
maxF a       b       = max a b

-- a closed percentage when it divides evenly
percent : ℕ → Formula → Formula
percent p (num a) = if ⌊ (a * p) % 100 ≟ 0 ⌋ then num ((a * p) / 100) else pct p (num a)
percent p a       = pct p a

-- positions are in half units
half : Formula → Formula
half (num a) = if ⌊ a % 2 ≟ 0 ⌋ then num (a / 2) else hlf (num a)
half a       = hlf a

enc : Expr ℕ → Formula
enc (pure v)                = var v
enc (impure (inj₁ E.Zero , _))   = num 0
enc (impure (inj₁ (E.Lit n) , _))  = num n
enc (impure (inj₁ E.Plus , k))   = plus (enc (k zero)) (enc (k (fsuc zero)))
enc (impure (inj₂ E.Sub , k))  = monus (enc (k zero)) (enc (k (fsuc zero)))
enc (impure (inj₁ E.Max , k))    = maxF (enc (k zero)) (enc (k (fsuc zero)))
enc (impure (inj₁ (E.Pct p) , k))  = percent p (enc (k tt))

-- folding closed subformulas, in ℕ: a closed node becomes its value, always
numOf : Formula → Maybe ℕ
numOf (num n) = just n
numOf _       = nothing

fold1 : (ℕ → ℕ) → (Formula → Formula) → Formula → Formula
fold1 f mk a with numOf a
... | just x  = num (f x)
... | nothing = mk a

fold2 : (ℕ → ℕ → ℕ) → (Formula → Formula → Formula) → Formula → Formula → Formula
fold2 f mk a b with numOf a | numOf b
... | just x | just y = num (f x y)
... | _      | _      = mk a b

-- `if a < b then x else y`; a closed comparison picks its branch
ltF : Formula → Formula → Formula → Formula → Formula
ltF a b x y with numOf a | numOf b
... | just u | just v = if u <ᵇ v then x else y
... | _      | _      = flt a b x y

plusN monusN maxN : Formula → Formula → Formula
plusN  = fold2 _+_ add
monusN = fold2 _∸_ sub
maxN   = fold2 _⊔_ max

percentN divF modF mulF : ℕ → Formula → Formula
percentN p = fold1 (λ x → (x * p) / 100) (pct p)
divF d     = fold1 (λ x → x / suc d) (fdiv d)
modF d     = fold1 (λ x → x % suc d) (fmod d)
mulF n     = fold1 (n *_) (fmul n)

encD : DExpr ℕ → Formula
encD (pure v)                                    = var v
encD (impure (inj₁ (inj₁ E.Zero) , _))           = num 0
encD (impure (inj₁ (inj₁ (E.Lit n)) , _))        = num n
encD (impure (inj₁ (inj₁ E.Plus) , k))           = plusN (encD (k zero)) (encD (k (fsuc zero)))
encD (impure (inj₁ (inj₁ E.Max) , k))            = maxN (encD (k zero)) (encD (k (fsuc zero)))
encD (impure (inj₁ (inj₁ (E.Pct p)) , k))        = percentN p (encD (k tt))
encD (impure (inj₁ (inj₂ E.Sub) , k))            = monusN (encD (k zero)) (encD (k (fsuc zero)))
encD (impure (inj₂ (Eu.DivBy d) , k))            = divF d (encD (k tt))
encD (impure (inj₂ (Eu.ModBy d) , k))            = modF d (encD (k tt))
encD (impure (inj₂ (Eu.MulLit n) , k))           = mulF n (encD (k tt))
encD (impure (inj₂ Eu.Lt , k))                   =
  ltF (encD (k zero)) (encD (k (fsuc zero))) (encD (k (fsuc (fsuc zero)))) (encD (k (fsuc (fsuc (fsuc zero)))))

------------------------------------------------------------------------
-- Equality of formulas

-- a formula is a rose tree: a tag (the constructor) with its numeric argument, and the subformulas
private
  Tok : Set
  Tok = ℕ × ℕ

  to : Formula → Rose Tok
  to (num n)       = node (0 , n) []
  to (var n)       = node (1 , n) []
  to (add a b)     = node (2 , 0) (to a ∷ to b ∷ [])
  to (sub a b)     = node (3 , 0) (to a ∷ to b ∷ [])
  to (max a b)     = node (4 , 0) (to a ∷ to b ∷ [])
  to (pct p a)     = node (5 , p) (to a ∷ [])
  to (hlf a)       = node (6 , 0) (to a ∷ [])
  to (fdiv d a)    = node (7 , d) (to a ∷ [])
  to (fmod d a)    = node (8 , d) (to a ∷ [])
  to (fmul n a)    = node (9 , n) (to a ∷ [])
  to (flt a b x y) = node (10 , 0) (to a ∷ to b ∷ to x ∷ to y ∷ [])

  from : Rose Tok → Formula
  from (node (0 , n)  _)                         = num n
  from (node (1 , n)  _)                         = var n
  from (node (2 , _)  (a ∷ b ∷ _))               = add (from a) (from b)
  from (node (3 , _)  (a ∷ b ∷ _))               = sub (from a) (from b)
  from (node (4 , _)  (a ∷ b ∷ _))               = max (from a) (from b)
  from (node (5 , p)  (a ∷ _))                   = pct p (from a)
  from (node (6 , _)  (a ∷ _))                   = hlf (from a)
  from (node (7 , d)  (a ∷ _))                   = fdiv d (from a)
  from (node (8 , d)  (a ∷ _))                   = fmod d (from a)
  from (node (9 , n)  (a ∷ _))                   = fmul n (from a)
  from (node (10 , _) (a ∷ b ∷ x ∷ y ∷ _))       = flt (from a) (from b) (from x) (from y)
  from _                                         = num 0

  from-to : ∀ f → from (to f) ≡ f
  from-to (num n)       = refl
  from-to (var n)       = refl
  from-to (add a b)     = cong₂ add (from-to a) (from-to b)
  from-to (sub a b)     = cong₂ sub (from-to a) (from-to b)
  from-to (max a b)     = cong₂ max (from-to a) (from-to b)
  from-to (pct p a)     = cong (pct p) (from-to a)
  from-to (hlf a)       = cong hlf (from-to a)
  from-to (fdiv d a)    = cong (fdiv d) (from-to a)
  from-to (fmod d a)    = cong (fmod d) (from-to a)
  from-to (fmul n a)    = cong (fmul n) (from-to a)
  from-to (flt a b x y) rewrite from-to a | from-to b | from-to x | from-to y = refl

formulaEq? : DecidableEquality Formula
formulaEq? = retract-dec to from from-to (roseEq? (ΣP.≡-dec ℕP._≟_ ℕP._≟_))
