{-# OPTIONS --safe --without-K #-}

-- The formulas shipped to the page.
--
-- A template's symbolic layout has a formula (`Slides.Diagram.Ordered`) at every coordinate.  The
-- backend ships it as a small tree the page evaluates in real numbers (`ev` in
-- `assets/animation.js`): a number, the parameter of a segment, `+`, `-` (real subtraction),
-- `m` (maximum), `["%", p, a]` ("p percent of a") and `["h", a]` (half of `a`, positions being
-- in half units), floor division `fdiv d`, remainder `fmod d` (real: `a - (d+1)·⌊a/(d+1)⌋`), a
-- literal factor `fmul n`, `flt a b x y` (`x` if `a < b` else `y`), minimum `fmin` and easing
-- `fease e`.  Closed subformulas are folded when the result is exact in ℚ (`fold1`, `fold2`): a
-- closed difference when the minuend is at least the subtrahend, a closed percentage when it
-- divides evenly, a half when the number is even, and every other operation on whole numbers
-- (sums, maxima, minima, floor division, remainder, factor, comparison: they are `ι`-homomorphisms,
-- `Slides.Diagram.Ordered.Properties`).  An easing is never folded: its value on a whole number
-- is a rational that the encoder must not compute (a Bézier is a 16-step bisection in ℚ).
--
-- This module is the data and the encoders, which is what the backend runs; what they mean
-- (the reading `⟦_⟧` in ℚ, and the proofs that the folds are exact) is
-- `Slides.Anim.Formula.Properties`.

module Slides.Anim.Formula where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (zero) renaming (suc to fsuc)
open import Data.Container.FreeMonad using (pure; impure)
open import Data.Integer using (ℤ)
import Data.Integer.Properties as ℤP
open import Data.Nat as ℕ using (ℕ; suc; _*_; _/_; _%_; _≤ᵇ_; _<ᵇ_; _∸_; _+_; _⊔_; _⊓_; _≟_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Unit using (tt; ⊤)
open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary.Decidable using (⌊_⌋)
import Data.Product.Properties as ΣP
import Data.Sum.Properties as SP
import Data.Unit.Properties as UP
import Data.Nat.Properties as ℕP

open import Slides.Diagram.Expr as E using (Expr)
open import Slides.Diagram.Euclid using (DExpr)
import Slides.Diagram.Euclid as Eu
open import Slides.Diagram.Ordered using (QExpr; weakenQ; weakenO; OrdOp; FloorOp; EaseOp; Lt; Min; DivBy; ModBy; MulLit; Ease)
open import Slides.Anim.Track using (Easing; Linear; Step; StepStart; Bezier)
open import Slides.DecEq

data Formula : Set where
  num  : ℕ → Formula                 -- a whole number
  var  : ℕ → Formula                 -- the parameter of a segment
  add sub max fmin : Formula → Formula → Formula
  pct  : ℕ → Formula → Formula       -- `p` percent of
  hlf  : Formula → Formula           -- half of
  fdiv fmod : ℕ → Formula → Formula  -- `fdiv d a`: ⌊a / (d+1)⌋, `fmod d a`: a - (d+1)·⌊a / (d+1)⌋
  fmul : ℕ → Formula → Formula       -- a literal factor
  flt  : Formula → Formula → Formula → Formula → Formula   -- `flt a b x y`: x if a < b else y
  fease : Easing → Formula → Formula -- an easing applied to a progress

isNum : Formula → Bool
isNum (num _) = true
isNum _       = false

------------------------------------------------------------------------
-- Folding closed subformulas, when exact

numOf : Formula → Maybe ℕ
numOf (num n) = just n
numOf _       = nothing

-- a closed node becomes its value `f x` when it has one (`f` is partial: `nothing` where the ℚ
-- reading of the node is not the ℕ one), else the node `mk` is built
foldOr : Maybe ℕ → Formula → Formula
foldOr (just n) _ = num n
foldOr nothing  g = g

fold1 : (ℕ → Maybe ℕ) → (Formula → Formula) → Formula → Formula
fold1 f mk a = foldOr (numOf a Maybe.>>= f) (mk a)

fold2 : (ℕ → ℕ → Maybe ℕ) → (Formula → Formula → Formula) → Formula → Formula → Formula
fold2 f mk a b = foldOr (numOf a Maybe.>>= λ x → numOf b Maybe.>>= f x) (mk a b)

-- the operations that are exact on whole numbers
tot1 : (ℕ → ℕ) → ℕ → Maybe ℕ
tot1 f x = just (f x)

tot2 : (ℕ → ℕ → ℕ) → ℕ → ℕ → Maybe ℕ
tot2 f x y = just (f x y)

-- ... and the ones that are exact on some
exactIf : Bool → ℕ → Maybe ℕ
exactIf true  n = just n
exactIf false _ = nothing

-- a closed difference is folded when it is not negative
plus maxF minF monus : Formula → Formula → Formula
plus  = fold2 (tot2 _+_) add
maxF  = fold2 (tot2 _⊔_) max
minF  = fold2 (tot2 _⊓_) fmin
monus = fold2 (λ a b → exactIf (b ≤ᵇ a) (a ∸ b)) sub

-- a closed percentage when it divides evenly; positions are in half units, so a half when the
-- number is even
percent : ℕ → Formula → Formula
percent p = fold1 (λ a → exactIf ⌊ (a * p) % 100 ≟ 0 ⌋ ((a * p) / 100)) (pct p)

half : Formula → Formula
half = fold1 (λ a → exactIf ⌊ a % 2 ≟ 0 ⌋ (a / 2)) hlf

divF modF mulF : ℕ → Formula → Formula
divF d = fold1 (tot1 (_/ suc d)) (fdiv d)
modF d = fold1 (tot1 (_% suc d)) (fmod d)
mulF n = fold1 (tot1 (n *_)) (fmul n)

-- `if a < b then x else y`; a closed comparison picks its branch
ltF : Formula → Formula → Formula → Formula → Formula
ltF a b x y with numOf a | numOf b
... | just u | just v = if u <ᵇ v then x else y
... | _      | _      = flt a b x y

-- the encoder: the shipped formula of a symbolic scalar (`Slides.Diagram.Ordered`)
enc : QExpr ℕ → Formula
enc (pure v)                                          = var v
enc (impure (inj₁ (inj₁ (inj₁ E.Zero)) , _))          = num 0
enc (impure (inj₁ (inj₁ (inj₁ (E.Lit n))) , _))       = num n
enc (impure (inj₁ (inj₁ (inj₁ E.Plus)) , k))          = plus (enc (k zero)) (enc (k (fsuc zero)))
enc (impure (inj₁ (inj₁ (inj₁ E.Max)) , k))           = maxF (enc (k zero)) (enc (k (fsuc zero)))
enc (impure (inj₁ (inj₁ (inj₁ (E.Pct p))) , k))       = percent p (enc (k tt))
enc (impure (inj₁ (inj₁ (inj₂ E.Sub)) , k))           = monus (enc (k zero)) (enc (k (fsuc zero)))
enc (impure (inj₁ (inj₂ (inj₁ Lt)) , k))              =
  ltF (enc (k zero)) (enc (k (fsuc zero))) (enc (k (fsuc (fsuc zero)))) (enc (k (fsuc (fsuc (fsuc zero)))))
enc (impure (inj₁ (inj₂ (inj₁ Min)) , k))             = minF (enc (k zero)) (enc (k (fsuc zero)))
enc (impure (inj₁ (inj₂ (inj₂ (DivBy d))) , k))       = divF d (enc (k tt))
enc (impure (inj₁ (inj₂ (inj₂ (ModBy d))) , k))       = modF d (enc (k tt))
enc (impure (inj₁ (inj₂ (inj₂ (MulLit n))) , k))      = mulF n (enc (k tt))
enc (impure (inj₂ (Ease e) , k))                      = fease e (enc (k tt))

-- a continuous template (`Expr`), through its weakening
encE : Expr ℕ → Formula
encE e = enc (weakenQ (weakenO e))

-- the discrete encoder (`Slides.Anim.DParam`, read in ℕ): a closed node always folds
monusN : Formula → Formula → Formula
monusN = fold2 (tot2 _∸_) sub

percentN : ℕ → Formula → Formula
percentN p = fold1 (tot1 (λ x → (x * p) / 100)) (pct p)

encD : DExpr ℕ → Formula
encD (pure v)                                    = var v
encD (impure (inj₁ (inj₁ E.Zero) , _))           = num 0
encD (impure (inj₁ (inj₁ (E.Lit n)) , _))        = num n
encD (impure (inj₁ (inj₁ E.Plus) , k))           = plus (encD (k zero)) (encD (k (fsuc zero)))
encD (impure (inj₁ (inj₁ E.Max) , k))            = maxF (encD (k zero)) (encD (k (fsuc zero)))
encD (impure (inj₁ (inj₁ (E.Pct p)) , k))        = percentN p (encD (k tt))
encD (impure (inj₁ (inj₂ E.Sub) , k))            = monusN (encD (k zero)) (encD (k (fsuc zero)))
encD (impure (inj₂ (Eu.DivBy d) , k))            = divF d (encD (k tt))
encD (impure (inj₂ (Eu.ModBy d) , k))            = modF d (encD (k tt))
encD (impure (inj₂ (Eu.MulLit n) , k))           = mulF n (encD (k tt))
encD (impure (inj₂ Eu.Lt , k))                   =
  ltF (encD (k zero)) (encD (k (fsuc zero))) (encD (k (fsuc (fsuc zero)))) (encD (k (fsuc (fsuc (fsuc zero)))))

------------------------------------------------------------------------
-- Equality of formulas

-- a formula is a rose tree: a tag (the constructor) with its numeric argument or its easing, and the subformulas
private
  Tok : Set
  Tok = (ℕ × ℕ) ⊎ Easing

  tk : ℕ → ℕ → Tok
  tk k n = inj₁ (k , n)

  to : Formula → Rose Tok
  to (num n)       = node (tk 0 n) []
  to (var n)       = node (tk 1 n) []
  to (add a b)     = node (tk 2 0) (to a ∷ to b ∷ [])
  to (sub a b)     = node (tk 3 0) (to a ∷ to b ∷ [])
  to (max a b)     = node (tk 4 0) (to a ∷ to b ∷ [])
  to (pct p a)     = node (tk 5 p) (to a ∷ [])
  to (hlf a)       = node (tk 6 0) (to a ∷ [])
  to (fdiv d a)    = node (tk 7 d) (to a ∷ [])
  to (fmod d a)    = node (tk 8 d) (to a ∷ [])
  to (fmul n a)    = node (tk 9 n) (to a ∷ [])
  to (flt a b x y) = node (tk 10 0) (to a ∷ to b ∷ to x ∷ to y ∷ [])
  to (fmin a b)    = node (tk 11 0) (to a ∷ to b ∷ [])
  to (fease e a)   = node (inj₂ e) (to a ∷ [])

  from : Rose Tok → Formula
  from (node (inj₁ (0 , n))  _)                  = num n
  from (node (inj₁ (1 , n))  _)                  = var n
  from (node (inj₁ (2 , _))  (a ∷ b ∷ _))        = add (from a) (from b)
  from (node (inj₁ (3 , _))  (a ∷ b ∷ _))        = sub (from a) (from b)
  from (node (inj₁ (4 , _))  (a ∷ b ∷ _))        = max (from a) (from b)
  from (node (inj₁ (5 , p))  (a ∷ _))            = pct p (from a)
  from (node (inj₁ (6 , _))  (a ∷ _))            = hlf (from a)
  from (node (inj₁ (7 , d))  (a ∷ _))            = fdiv d (from a)
  from (node (inj₁ (8 , d))  (a ∷ _))            = fmod d (from a)
  from (node (inj₁ (9 , n))  (a ∷ _))            = fmul n (from a)
  from (node (inj₁ (10 , _)) (a ∷ b ∷ x ∷ y ∷ _)) = flt (from a) (from b) (from x) (from y)
  from (node (inj₁ (11 , _)) (a ∷ b ∷ _))        = fmin (from a) (from b)
  from (node (inj₂ e)        (a ∷ _))            = fease e (from a)
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
  from-to (fmin a b)    = cong₂ fmin (from-to a) (from-to b)
  from-to (fease e a)   = cong (fease e) (from-to a)

-- decidable equality of easings: a retract of sums and products of numbers
easingEq? : DecidableEquality Easing
easingEq? = retract-dec eto efrom ert
  (SP.≡-dec UP._≟_ (SP.≡-dec UP._≟_ (SP.≡-dec UP._≟_ (ΣP.≡-dec ℤP._≟_ (ΣP.≡-dec ℤP._≟_ (ΣP.≡-dec ℤP._≟_ ℤP._≟_))))))
  where
    eto : Easing → ⊤ ⊎ ⊤ ⊎ ⊤ ⊎ (ℤ × ℤ × ℤ × ℤ)
    eto Linear           = inj₁ tt
    eto Step             = inj₂ (inj₁ tt)
    eto StepStart        = inj₂ (inj₂ (inj₁ tt))
    eto (Bezier a b c d) = inj₂ (inj₂ (inj₂ (a , b , c , d)))
    efrom : ⊤ ⊎ ⊤ ⊎ ⊤ ⊎ (ℤ × ℤ × ℤ × ℤ) → Easing
    efrom (inj₁ _)                        = Linear
    efrom (inj₂ (inj₁ _))                 = Step
    efrom (inj₂ (inj₂ (inj₁ _)))          = StepStart
    efrom (inj₂ (inj₂ (inj₂ (a , b , c , d)))) = Bezier a b c d
    ert : ∀ e → efrom (eto e) ≡ e
    ert Linear           = refl
    ert Step             = refl
    ert StepStart        = refl
    ert (Bezier _ _ _ _) = refl

formulaEq? : DecidableEquality Formula
formulaEq? = retract-dec to from from-to
  (roseEq? (SP.≡-dec (ΣP.≡-dec ℕP._≟_ ℕP._≟_) easingEq?))
