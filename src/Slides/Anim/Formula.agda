{-# OPTIONS --safe --without-K #-}

-- The formulas shipped to the page, and what they mean.
--
-- A template's symbolic layout has a formula (`Slides.Diagram.Expr`) at every coordinate.  The
-- backend ships it as a small tree the page evaluates in real numbers (`ev` in
-- `assets/animation.js`): a number, the parameter of a segment, `+`, `-` (real subtraction),
-- `m` (maximum), `["%", p, a]` ("p percent of a") and `["h", a]` (half of `a`, positions being
-- in half units).  Closed subformulas are folded when the result is exact: a closed
-- difference when the minuend is at least the subtrahend, a closed percentage when it divides
-- evenly, a half when the number is even.  Sums and maxima of closed formulas always fold.
--
-- `⟦_⟧` is the meaning of a shipped formula in ℚ (`ratOps`, as `Slides.Anim.Continuous`).
--
--   * `enc-sem`: `⟦ enc e ⟧ ρ ≡ evalWith ratOps ρ e` for every assignment `ρ`: shipping the
--     folded formula means what the symbolic coordinate means in ℚ.  So the folds are exact.
--   * `half-sem`: `⟦ half f ⟧ ρ ≡ (1/2) · ⟦ f ⟧ ρ`.
--   * `enc-num`: if `enc e` folded to the number `n`, then `e` evaluates to `n` in ℕ at *every*
--     assignment (the all-zero one in particular, which is where the page's base elements are
--     taken).
--
-- Not proved: that the page's `ev` computes `⟦_⟧` (it does so in floating point; checked by
-- `tests/browser/anim-ref.mjs`).

module Slides.Anim.Formula where

open import Data.Bool using (Bool; true; false; if_then_else_; T)
open import Data.Fin using (zero; suc)
open import Data.Container.FreeMonad using (pure; impure)
open import Data.Integer as ℤ using (+_)
import Data.Integer.Properties as ℤP
open import Data.Integer.Tactic.RingSolver using (solve-∀)
open import Data.Nat as ℕ using (ℕ; _*_; _/_; _%_; _≤ᵇ_; _∸_; _+_; _⊔_; _≟_)
import Data.Nat.DivMod as ℕDM
import Data.Nat.Properties as ℕP
open import Data.Rational as ℚ using (ℚ)
import Data.Rational.Properties as ℚP
import Data.Rational.Unnormalised.Properties as ℚᵘP
open import Data.Rational.Unnormalised using (*≡*)
open import Data.Product using (_,_; _×_; ∃; ∃₂)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Slides.Diagram.Expr using (Expr; ExprOp; evalWith; eval)
import Slides.Diagram.Expr as E
open import Slides.Diagram.ExprQ using (exact%)
open import Slides.Diagram.NatQ
open import Slides.Diagram.Scalar using (ratOps; natOps)

data Formula : Set where
  num  : ℕ → Formula                 -- a whole number
  var  : ℕ → Formula                 -- the parameter of a segment
  add sub max : Formula → Formula → Formula
  pct  : ℕ → Formula → Formula       -- `p` percent of
  hlf  : Formula → Formula           -- half of

-- the meaning in ℚ, given the parameters of the segments
⟦_⟧ : Formula → (ℕ → ℚ) → ℚ
⟦ num n ⟧     ρ = ι n
⟦ var i ⟧     ρ = ρ i
⟦ add a b ⟧   ρ = ⟦ a ⟧ ρ ℚ.+ ⟦ b ⟧ ρ
⟦ sub a b ⟧   ρ = ⟦ a ⟧ ρ ℚ.- ⟦ b ⟧ ρ
⟦ max a b ⟧   ρ = ⟦ a ⟧ ρ ℚ.⊔ ⟦ b ⟧ ρ
⟦ pct p a ⟧   ρ = (+ p ℚ./ 100) ℚ.* ⟦ a ⟧ ρ
⟦ hlf a ⟧     ρ = (+ 1 ℚ./ 2) ℚ.* ⟦ a ⟧ ρ

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
enc (impure (E.Zero , _))   = num 0
enc (impure (E.Lit n , _))  = num n
enc (impure (E.Plus , k))   = plus (enc (k zero)) (enc (k (suc zero)))
enc (impure (E.Monus , k))  = monus (enc (k zero)) (enc (k (suc zero)))
enc (impure (E.Max , k))    = maxF (enc (k zero)) (enc (k (suc zero)))
enc (impure (E.Pct p , k))  = percent p (enc (k tt))

------------------------------------------------------------------------
-- The folds are exact

-- half of an even number
exactHalf : ∀ a → a % 2 ≡ 0 → ι (a / 2) ≡ (+ 1 ℚ./ 2) ℚ.* ι a
exactHalf a h = ℚP.toℚᵘ-injective
  (ℚᵘP.≃-trans (toℚᵘ-ι q)
  (ℚᵘP.≃-trans (*≡* (trans (sym (ℤP.pos-* q 2)) (trans (cong +_ (sym eq)) (lem (+ a)))))
  (ℚᵘP.≃-sym (ℚᵘP.≃-trans (ℚP.toℚᵘ-homo-* (+ 1 ℚ./ 2) (ι a))
                          (ℚᵘP.*-cong (toℚᵘ-/ (+ 1) 1) (toℚᵘ-ι a))))))
  where
    q = a / 2
    eq : a ≡ q * 2
    eq = trans (ℕDM.m≡m%n+[m/n]*n a 2) (cong (_+ q * 2) h)
    lem : ∀ x → x ≡ + 1 ℤ.* x ℤ.* + 1
    lem = solve-∀

plus-sem : ∀ a b ρ → ⟦ plus a b ⟧ ρ ≡ ⟦ a ⟧ ρ ℚ.+ ⟦ b ⟧ ρ
plus-sem (num a) (num b) ρ = ι-+ a b
plus-sem (var _) b ρ = refl
plus-sem (add _ _) b ρ = refl
plus-sem (sub _ _) b ρ = refl
plus-sem (max _ _) b ρ = refl
plus-sem (pct _ _) b ρ = refl
plus-sem (hlf _) b ρ = refl
plus-sem (num a) (var _) ρ = refl
plus-sem (num a) (add _ _) ρ = refl
plus-sem (num a) (sub _ _) ρ = refl
plus-sem (num a) (max _ _) ρ = refl
plus-sem (num a) (pct _ _) ρ = refl
plus-sem (num a) (hlf _) ρ = refl

maxF-sem : ∀ a b ρ → ⟦ maxF a b ⟧ ρ ≡ ⟦ a ⟧ ρ ℚ.⊔ ⟦ b ⟧ ρ
maxF-sem (num a) (num b) ρ = ι-⊔ a b
maxF-sem (var _) b ρ = refl
maxF-sem (add _ _) b ρ = refl
maxF-sem (sub _ _) b ρ = refl
maxF-sem (max _ _) b ρ = refl
maxF-sem (pct _ _) b ρ = refl
maxF-sem (hlf _) b ρ = refl
maxF-sem (num a) (var _) ρ = refl
maxF-sem (num a) (add _ _) ρ = refl
maxF-sem (num a) (sub _ _) ρ = refl
maxF-sem (num a) (max _ _) ρ = refl
maxF-sem (num a) (pct _ _) ρ = refl
maxF-sem (num a) (hlf _) ρ = refl

monus-sem : ∀ a b ρ → ⟦ monus a b ⟧ ρ ≡ ⟦ a ⟧ ρ ℚ.- ⟦ b ⟧ ρ
monus-sem (num a) (num b) ρ with b ≤ᵇ a in eq
... | true  = ι-∸ a b (ℕP.≤ᵇ⇒≤ b a (subst T (sym eq) tt))
... | false = refl
monus-sem (var _) b ρ = refl
monus-sem (add _ _) b ρ = refl
monus-sem (sub _ _) b ρ = refl
monus-sem (max _ _) b ρ = refl
monus-sem (pct _ _) b ρ = refl
monus-sem (hlf _) b ρ = refl
monus-sem (num a) (var _) ρ = refl
monus-sem (num a) (add _ _) ρ = refl
monus-sem (num a) (sub _ _) ρ = refl
monus-sem (num a) (max _ _) ρ = refl
monus-sem (num a) (pct _ _) ρ = refl
monus-sem (num a) (hlf _) ρ = refl

percent-sem : ∀ p a ρ → ⟦ percent p a ⟧ ρ ≡ (+ p ℚ./ 100) ℚ.* ⟦ a ⟧ ρ
percent-sem p (num a) ρ with (a * p) % 100 ≟ 0
... | yes h = exact% p a h
... | no _  = refl
percent-sem p (var _) ρ = refl
percent-sem p (add _ _) ρ = refl
percent-sem p (sub _ _) ρ = refl
percent-sem p (max _ _) ρ = refl
percent-sem p (pct _ _) ρ = refl
percent-sem p (hlf _) ρ = refl

half-sem : ∀ a ρ → ⟦ half a ⟧ ρ ≡ (+ 1 ℚ./ 2) ℚ.* ⟦ a ⟧ ρ
half-sem (num a) ρ with a % 2 ≟ 0
... | yes h = exactHalf a h
... | no _  = refl
half-sem (var _) ρ = refl
half-sem (add _ _) ρ = refl
half-sem (sub _ _) ρ = refl
half-sem (max _ _) ρ = refl
half-sem (pct _ _) ρ = refl
half-sem (hlf _) ρ = refl

-- Shipping the folded formula means what the symbolic coordinate means in ℚ.
enc-sem : ∀ (e : Expr ℕ) (ρ : ℕ → ℚ) → ⟦ enc e ⟧ ρ ≡ evalWith ratOps ρ e
enc-sem (pure v) ρ = refl
enc-sem (impure (E.Zero , _)) ρ = refl
enc-sem (impure (E.Lit n , _)) ρ = refl
enc-sem (impure (E.Plus , k)) ρ =
  trans (plus-sem (enc (k zero)) (enc (k (suc zero))) ρ) (cong₂ ℚ._+_ (enc-sem (k zero) ρ) (enc-sem (k (suc zero)) ρ))
enc-sem (impure (E.Monus , k)) ρ =
  trans (monus-sem (enc (k zero)) (enc (k (suc zero))) ρ) (cong₂ ℚ._-_ (enc-sem (k zero) ρ) (enc-sem (k (suc zero)) ρ))
enc-sem (impure (E.Max , k)) ρ =
  trans (maxF-sem (enc (k zero)) (enc (k (suc zero))) ρ) (cong₂ ℚ._⊔_ (enc-sem (k zero) ρ) (enc-sem (k (suc zero)) ρ))
enc-sem (impure (E.Pct p , k)) ρ =
  trans (percent-sem p (enc (k tt)) ρ) (cong ((+ p ℚ./ 100) ℚ.*_) (enc-sem (k tt) ρ))

------------------------------------------------------------------------
-- A folded number is the value of the expression at every assignment, in ℕ

private
  plus-inv : ∀ a b n → plus a b ≡ num n → ∃₂ λ x y → a ≡ num x × b ≡ num y × x + y ≡ n
  plus-inv (num x) (num y) n refl = x , y , refl , refl , refl
  plus-inv (num x) (var _) n ()
  plus-inv (num x) (add _ _) n ()
  plus-inv (num x) (sub _ _) n ()
  plus-inv (num x) (max _ _) n ()
  plus-inv (num x) (pct _ _) n ()
  plus-inv (num x) (hlf _) n ()
  plus-inv (var _) b n ()
  plus-inv (add _ _) b n ()
  plus-inv (sub _ _) b n ()
  plus-inv (max _ _) b n ()
  plus-inv (pct _ _) b n ()
  plus-inv (hlf _) b n ()

  maxF-inv : ∀ a b n → maxF a b ≡ num n → ∃₂ λ x y → a ≡ num x × b ≡ num y × x ⊔ y ≡ n
  maxF-inv (num x) (num y) n refl = x , y , refl , refl , refl
  maxF-inv (num x) (var _) n ()
  maxF-inv (num x) (add _ _) n ()
  maxF-inv (num x) (sub _ _) n ()
  maxF-inv (num x) (max _ _) n ()
  maxF-inv (num x) (pct _ _) n ()
  maxF-inv (num x) (hlf _) n ()
  maxF-inv (var _) b n ()
  maxF-inv (add _ _) b n ()
  maxF-inv (sub _ _) b n ()
  maxF-inv (max _ _) b n ()
  maxF-inv (pct _ _) b n ()
  maxF-inv (hlf _) b n ()

  monus-inv : ∀ a b n → monus a b ≡ num n → ∃₂ λ x y → a ≡ num x × b ≡ num y × x ∸ y ≡ n
  monus-inv (num x) (num y) n h with y ≤ᵇ x
  monus-inv (num x) (num y) n refl | true  = x , y , refl , refl , refl
  monus-inv (num x) (num y) n ()   | false
  monus-inv (num x) (var _) n ()
  monus-inv (num x) (add _ _) n ()
  monus-inv (num x) (sub _ _) n ()
  monus-inv (num x) (max _ _) n ()
  monus-inv (num x) (pct _ _) n ()
  monus-inv (num x) (hlf _) n ()
  monus-inv (var _) b n ()
  monus-inv (add _ _) b n ()
  monus-inv (sub _ _) b n ()
  monus-inv (max _ _) b n ()
  monus-inv (pct _ _) b n ()
  monus-inv (hlf _) b n ()

  percent-inv : ∀ p a n → percent p a ≡ num n → ∃ λ x → a ≡ num x × (x * p) / 100 ≡ n
  percent-inv p (num x) n h with (x * p) % 100 ≟ 0
  percent-inv p (num x) n refl | yes _ = x , refl , refl
  percent-inv p (num x) n ()   | no _
  percent-inv p (var _) n ()
  percent-inv p (add _ _) n ()
  percent-inv p (sub _ _) n ()
  percent-inv p (max _ _) n ()
  percent-inv p (pct _ _) n ()
  percent-inv p (hlf _) n ()

enc-num : ∀ (e : Expr ℕ) n → enc e ≡ num n → ∀ (ρ : ℕ → ℕ) → eval ρ e ≡ n
enc-num (pure v) n () ρ
enc-num (impure (E.Zero , _)) n refl ρ = refl
enc-num (impure (E.Lit m , _)) n refl ρ = refl
enc-num (impure (E.Plus , k)) n h ρ with plus-inv (enc (k zero)) (enc (k (suc zero))) n h
... | x , y , e₁ , e₂ , refl = cong₂ _+_ (enc-num (k zero) x e₁ ρ) (enc-num (k (suc zero)) y e₂ ρ)
enc-num (impure (E.Monus , k)) n h ρ with monus-inv (enc (k zero)) (enc (k (suc zero))) n h
... | x , y , e₁ , e₂ , refl = cong₂ _∸_ (enc-num (k zero) x e₁ ρ) (enc-num (k (suc zero)) y e₂ ρ)
enc-num (impure (E.Max , k)) n h ρ with maxF-inv (enc (k zero)) (enc (k (suc zero))) n h
... | x , y , e₁ , e₂ , refl = cong₂ _⊔_ (enc-num (k zero) x e₁ ρ) (enc-num (k (suc zero)) y e₂ ρ)
enc-num (impure (E.Pct p , k)) n h ρ with percent-inv p (enc (k tt)) n h
... | x , e₁ , refl = cong (λ v → (v * p) / 100) (enc-num (k tt) x e₁ ρ)

-- `half` of a number only folds when the number is even, and then to its half
half-num-inv : ∀ a n → half a ≡ num n → ∃ λ x → a ≡ num x × x % 2 ≡ 0 × x / 2 ≡ n
half-num-inv (num x) n h with x % 2 ≟ 0
half-num-inv (num x) n refl | yes e = x , refl , e , refl
half-num-inv (num x) n ()   | no _
half-num-inv (var _) n ()
half-num-inv (add _ _) n ()
half-num-inv (sub _ _) n ()
half-num-inv (max _ _) n ()
half-num-inv (pct _ _) n ()
half-num-inv (hlf _) n ()
