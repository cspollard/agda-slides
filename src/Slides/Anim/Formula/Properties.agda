{-# OPTIONS --safe --without-K #-}

-- What the shipped formulas mean (`Slides.Anim.Formula` defines them and the encoders).
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

module Slides.Anim.Formula.Properties where

open import Data.Bool using (true; false; if_then_else_; T)
open import Data.Fin using (zero) renaming (suc to fsuc)
open import Data.Container.FreeMonad using (pure; impure)
open import Data.Integer as ℤ using (+_)
import Data.Integer.Properties as ℤP
open import Data.Integer.Tactic.RingSolver using (solve-∀)
open import Data.Nat as ℕ using (ℕ; suc; _*_; _/_; _%_; _≤ᵇ_; _<ᵇ_; _∸_; _+_; _⊔_; _≟_)
import Data.Nat.DivMod as ℕDM
import Data.Nat.Properties as ℕP
open import Data.Rational as ℚ using (ℚ)
import Data.Rational.Properties as ℚP
import Data.Rational.Unnormalised.Properties as ℚᵘP
open import Data.Rational.Unnormalised using (*≡*)
open import Data.Product using (_,_; _×_; ∃; ∃₂)
open import Data.Maybe using (just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Slides.Diagram.Expr using (Expr; evalWith; eval)
import Slides.Diagram.Expr as E
open import Slides.Diagram.Euclid using (DExpr; evalD; natD)
import Slides.Diagram.Euclid as Eu
open import Slides.Diagram.Expr.Properties.Faithful using (exact%)
open import Slides.Diagram.NatQ
open import Slides.Diagram.NatQ.Properties
open import Slides.Diagram.NatQ.Properties
open import Slides.Diagram.Scalar using (ratOps)
open import Slides.Anim.Formula

flr : ℚ → ℕ
flr q = ℤ.∣ ℚ.⌊ q ⌋ ∣

-- the meaning in ℚ, given the parameters of the segments
⟦_⟧ : Formula → (ℕ → ℚ) → ℚ
⟦ num n ⟧     ρ = ι n
⟦ var i ⟧     ρ = ρ i
⟦ add a b ⟧   ρ = ⟦ a ⟧ ρ ℚ.+ ⟦ b ⟧ ρ
⟦ sub a b ⟧   ρ = ⟦ a ⟧ ρ ℚ.- ⟦ b ⟧ ρ
⟦ max a b ⟧   ρ = ⟦ a ⟧ ρ ℚ.⊔ ⟦ b ⟧ ρ
⟦ pct p a ⟧   ρ = (+ p ℚ./ 100) ℚ.* ⟦ a ⟧ ρ
⟦ hlf a ⟧     ρ = (+ 1 ℚ./ 2) ℚ.* ⟦ a ⟧ ρ
-- The Euclidean nodes have no meaning in ℚ (floor division is not exact), and the continuous
-- encoder `enc` never produces them; they are read by flooring their arguments, so that `⟦_⟧`
-- is total.  Their meaning is `⟦_⟧ᴺ` below.
⟦ fdiv d a ⟧   ρ = ι (flr (⟦ a ⟧ ρ) / suc d)
⟦ fmod d a ⟧   ρ = ι (flr (⟦ a ⟧ ρ) % suc d)
⟦ fmul n a ⟧   ρ = ι (n * flr (⟦ a ⟧ ρ))
⟦ flt a b x y ⟧ ρ = if ⟦ b ⟧ ρ ℚ.≤ᵇ ⟦ a ⟧ ρ then ⟦ y ⟧ ρ else ⟦ x ⟧ ρ

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
plus-sem (fdiv _ _) b ρ = refl
plus-sem (fmod _ _) b ρ = refl
plus-sem (fmul _ _) b ρ = refl
plus-sem (flt _ _ _ _) b ρ = refl
plus-sem (num a) (var _) ρ = refl
plus-sem (num a) (add _ _) ρ = refl
plus-sem (num a) (sub _ _) ρ = refl
plus-sem (num a) (max _ _) ρ = refl
plus-sem (num a) (pct _ _) ρ = refl
plus-sem (num a) (hlf _) ρ = refl
plus-sem (num a) (fdiv _ _) ρ = refl
plus-sem (num a) (fmod _ _) ρ = refl
plus-sem (num a) (fmul _ _) ρ = refl
plus-sem (num a) (flt _ _ _ _) ρ = refl

maxF-sem : ∀ a b ρ → ⟦ maxF a b ⟧ ρ ≡ ⟦ a ⟧ ρ ℚ.⊔ ⟦ b ⟧ ρ
maxF-sem (num a) (num b) ρ = ι-⊔ a b
maxF-sem (var _) b ρ = refl
maxF-sem (add _ _) b ρ = refl
maxF-sem (sub _ _) b ρ = refl
maxF-sem (max _ _) b ρ = refl
maxF-sem (pct _ _) b ρ = refl
maxF-sem (hlf _) b ρ = refl
maxF-sem (fdiv _ _) b ρ = refl
maxF-sem (fmod _ _) b ρ = refl
maxF-sem (fmul _ _) b ρ = refl
maxF-sem (flt _ _ _ _) b ρ = refl
maxF-sem (num a) (var _) ρ = refl
maxF-sem (num a) (add _ _) ρ = refl
maxF-sem (num a) (sub _ _) ρ = refl
maxF-sem (num a) (max _ _) ρ = refl
maxF-sem (num a) (pct _ _) ρ = refl
maxF-sem (num a) (hlf _) ρ = refl
maxF-sem (num a) (fdiv _ _) ρ = refl
maxF-sem (num a) (fmod _ _) ρ = refl
maxF-sem (num a) (fmul _ _) ρ = refl
maxF-sem (num a) (flt _ _ _ _) ρ = refl

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
monus-sem (fdiv _ _) b ρ = refl
monus-sem (fmod _ _) b ρ = refl
monus-sem (fmul _ _) b ρ = refl
monus-sem (flt _ _ _ _) b ρ = refl
monus-sem (num a) (var _) ρ = refl
monus-sem (num a) (add _ _) ρ = refl
monus-sem (num a) (sub _ _) ρ = refl
monus-sem (num a) (max _ _) ρ = refl
monus-sem (num a) (pct _ _) ρ = refl
monus-sem (num a) (hlf _) ρ = refl
monus-sem (num a) (fdiv _ _) ρ = refl
monus-sem (num a) (fmod _ _) ρ = refl
monus-sem (num a) (fmul _ _) ρ = refl
monus-sem (num a) (flt _ _ _ _) ρ = refl

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
percent-sem p (fdiv _ _) ρ = refl
percent-sem p (fmod _ _) ρ = refl
percent-sem p (fmul _ _) ρ = refl
percent-sem p (flt _ _ _ _) ρ = refl

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
half-sem (fdiv _ _) ρ = refl
half-sem (fmod _ _) ρ = refl
half-sem (fmul _ _) ρ = refl
half-sem (flt _ _ _ _) ρ = refl

-- Shipping the folded formula means what the symbolic coordinate means in ℚ.
enc-sem : ∀ (e : Expr ℕ) (ρ : ℕ → ℚ) → ⟦ enc e ⟧ ρ ≡ evalWith ratOps ρ e
enc-sem (pure v) ρ = refl
enc-sem (impure (inj₁ E.Zero , _)) ρ = refl
enc-sem (impure (inj₁ (E.Lit n) , _)) ρ = refl
enc-sem (impure (inj₁ E.Plus , k)) ρ =
  trans (plus-sem (enc (k zero)) (enc (k (fsuc zero))) ρ) (cong₂ ℚ._+_ (enc-sem (k zero) ρ) (enc-sem (k (fsuc zero)) ρ))
enc-sem (impure (inj₂ E.Sub , k)) ρ =
  trans (monus-sem (enc (k zero)) (enc (k (fsuc zero))) ρ) (cong₂ ℚ._-_ (enc-sem (k zero) ρ) (enc-sem (k (fsuc zero)) ρ))
enc-sem (impure (inj₁ E.Max , k)) ρ =
  trans (maxF-sem (enc (k zero)) (enc (k (fsuc zero))) ρ) (cong₂ ℚ._⊔_ (enc-sem (k zero) ρ) (enc-sem (k (fsuc zero)) ρ))
enc-sem (impure (inj₁ (E.Pct p) , k)) ρ =
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
  plus-inv (num x) (fdiv _ _) n ()
  plus-inv (num x) (fmod _ _) n ()
  plus-inv (num x) (fmul _ _) n ()
  plus-inv (num x) (flt _ _ _ _) n ()
  plus-inv (var _) b n ()
  plus-inv (add _ _) b n ()
  plus-inv (sub _ _) b n ()
  plus-inv (max _ _) b n ()
  plus-inv (pct _ _) b n ()
  plus-inv (hlf _) b n ()
  plus-inv (fdiv _ _) b n ()
  plus-inv (fmod _ _) b n ()
  plus-inv (fmul _ _) b n ()
  plus-inv (flt _ _ _ _) b n ()

  maxF-inv : ∀ a b n → maxF a b ≡ num n → ∃₂ λ x y → a ≡ num x × b ≡ num y × x ⊔ y ≡ n
  maxF-inv (num x) (num y) n refl = x , y , refl , refl , refl
  maxF-inv (num x) (var _) n ()
  maxF-inv (num x) (add _ _) n ()
  maxF-inv (num x) (sub _ _) n ()
  maxF-inv (num x) (max _ _) n ()
  maxF-inv (num x) (pct _ _) n ()
  maxF-inv (num x) (hlf _) n ()
  maxF-inv (num x) (fdiv _ _) n ()
  maxF-inv (num x) (fmod _ _) n ()
  maxF-inv (num x) (fmul _ _) n ()
  maxF-inv (num x) (flt _ _ _ _) n ()
  maxF-inv (var _) b n ()
  maxF-inv (add _ _) b n ()
  maxF-inv (sub _ _) b n ()
  maxF-inv (max _ _) b n ()
  maxF-inv (pct _ _) b n ()
  maxF-inv (hlf _) b n ()
  maxF-inv (fdiv _ _) b n ()
  maxF-inv (fmod _ _) b n ()
  maxF-inv (fmul _ _) b n ()
  maxF-inv (flt _ _ _ _) b n ()

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
  monus-inv (num x) (fdiv _ _) n ()
  monus-inv (num x) (fmod _ _) n ()
  monus-inv (num x) (fmul _ _) n ()
  monus-inv (num x) (flt _ _ _ _) n ()
  monus-inv (var _) b n ()
  monus-inv (add _ _) b n ()
  monus-inv (sub _ _) b n ()
  monus-inv (max _ _) b n ()
  monus-inv (pct _ _) b n ()
  monus-inv (hlf _) b n ()
  monus-inv (fdiv _ _) b n ()
  monus-inv (fmod _ _) b n ()
  monus-inv (fmul _ _) b n ()
  monus-inv (flt _ _ _ _) b n ()

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
  percent-inv p (fdiv _ _) n ()
  percent-inv p (fmod _ _) n ()
  percent-inv p (fmul _ _) n ()
  percent-inv p (flt _ _ _ _) n ()

enc-num : ∀ (e : Expr ℕ) n → enc e ≡ num n → ∀ (ρ : ℕ → ℕ) → eval ρ e ≡ n
enc-num (pure v) n () ρ
enc-num (impure (inj₁ E.Zero , _)) n refl ρ = refl
enc-num (impure (inj₁ (E.Lit m) , _)) n refl ρ = refl
enc-num (impure (inj₁ E.Plus , k)) n h ρ with plus-inv (enc (k zero)) (enc (k (fsuc zero))) n h
... | x , y , e₁ , e₂ , refl = cong₂ _+_ (enc-num (k zero) x e₁ ρ) (enc-num (k (fsuc zero)) y e₂ ρ)
enc-num (impure (inj₂ E.Sub , k)) n h ρ with monus-inv (enc (k zero)) (enc (k (fsuc zero))) n h
... | x , y , e₁ , e₂ , refl = cong₂ _∸_ (enc-num (k zero) x e₁ ρ) (enc-num (k (fsuc zero)) y e₂ ρ)
enc-num (impure (inj₁ E.Max , k)) n h ρ with maxF-inv (enc (k zero)) (enc (k (fsuc zero))) n h
... | x , y , e₁ , e₂ , refl = cong₂ _⊔_ (enc-num (k zero) x e₁ ρ) (enc-num (k (fsuc zero)) y e₂ ρ)
enc-num (impure (inj₁ (E.Pct p) , k)) n h ρ with percent-inv p (enc (k tt)) n h
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
half-num-inv (fdiv _ _) n ()
half-num-inv (fmod _ _) n ()
half-num-inv (fmul _ _) n ()
half-num-inv (flt _ _ _ _) n ()

------------------------------------------------------------------------
-- Discrete templates: the same formulas, read in ℕ
--
-- A discrete template (`Slides.Diagram.Euclid`) is evaluated in ℕ at the integer tick, so the
-- page reads its formulas in ℕ too: `-` is the monus, `%` rounds down, `fdiv`/`fmod`/`flt`/`fmul`
-- are floor division, remainder, comparison and a literal factor (`⟦_⟧ᴺ`).  No exactness
-- condition is needed: folding a closed subformula uses the very same operation as reading it,
-- so `encD-semN` is an equation without hypotheses (unlike `enc-sem` in ℚ, where the folds are
-- only done when exact).  The one place a rational appears is the output, positions being in
-- half units: `⟦_⟧ᴰ` is `⟦_⟧ᴺ` into ℚ, except that the outermost `hlf` is a real half.

⟦_⟧ᴺ : Formula → (ℕ → ℕ) → ℕ
⟦ num n ⟧ᴺ      ρ = n
⟦ var i ⟧ᴺ      ρ = ρ i
⟦ add a b ⟧ᴺ    ρ = ⟦ a ⟧ᴺ ρ + ⟦ b ⟧ᴺ ρ
⟦ sub a b ⟧ᴺ    ρ = ⟦ a ⟧ᴺ ρ ∸ ⟦ b ⟧ᴺ ρ
⟦ max a b ⟧ᴺ    ρ = ⟦ a ⟧ᴺ ρ ⊔ ⟦ b ⟧ᴺ ρ
⟦ pct p a ⟧ᴺ    ρ = (⟦ a ⟧ᴺ ρ * p) / 100
⟦ hlf a ⟧ᴺ      ρ = ⟦ a ⟧ᴺ ρ / 2        -- only ever the outermost node, read by `⟦_⟧ᴰ`
⟦ fdiv d a ⟧ᴺ   ρ = ⟦ a ⟧ᴺ ρ / suc d
⟦ fmod d a ⟧ᴺ   ρ = ⟦ a ⟧ᴺ ρ % suc d
⟦ fmul n a ⟧ᴺ   ρ = n * ⟦ a ⟧ᴺ ρ
⟦ flt a b x y ⟧ᴺ ρ = if ⟦ a ⟧ᴺ ρ <ᵇ ⟦ b ⟧ᴺ ρ then ⟦ x ⟧ᴺ ρ else ⟦ y ⟧ᴺ ρ

⟦_⟧ᴰ : Formula → (ℕ → ℕ) → ℚ
⟦ hlf a ⟧ᴰ ρ = (+ 1 ℚ./ 2) ℚ.* ι (⟦ a ⟧ᴺ ρ)
⟦ f ⟧ᴰ     ρ = ι (⟦ f ⟧ᴺ ρ)

numOf-eq : ∀ f {n} → numOf f ≡ just n → f ≡ num n
numOf-eq (num m)       refl = refl
numOf-eq (var _)       ()
numOf-eq (add _ _)     ()
numOf-eq (sub _ _)     ()
numOf-eq (max _ _)     ()
numOf-eq (pct _ _)     ()
numOf-eq (hlf _)       ()
numOf-eq (fdiv _ _)    ()
numOf-eq (fmod _ _)    ()
numOf-eq (fmul _ _)    ()
numOf-eq (flt _ _ _ _) ()

------------------------------------------------------------------------
-- The discrete encoder is exact: `encD-semN`

private
  fold1-semN : ∀ f mk a ρ → ⟦ mk a ⟧ᴺ ρ ≡ f (⟦ a ⟧ᴺ ρ) → ⟦ fold1 f mk a ⟧ᴺ ρ ≡ f (⟦ a ⟧ᴺ ρ)
  fold1-semN f mk a ρ h with numOf a in eq
  ... | just x rewrite numOf-eq a eq = refl
  ... | nothing = h

  fold2-semN : ∀ f mk a b ρ → ⟦ mk a b ⟧ᴺ ρ ≡ f (⟦ a ⟧ᴺ ρ) (⟦ b ⟧ᴺ ρ) →
               ⟦ fold2 f mk a b ⟧ᴺ ρ ≡ f (⟦ a ⟧ᴺ ρ) (⟦ b ⟧ᴺ ρ)
  fold2-semN f mk a b ρ h with numOf a in ea | numOf b in eb
  ... | just x | just y rewrite numOf-eq a ea | numOf-eq b eb = refl
  ... | just _ | nothing = h
  ... | nothing | _ = h

  if-semN : ∀ c x y ρ → ⟦ if c then x else y ⟧ᴺ ρ ≡ (if c then ⟦ x ⟧ᴺ ρ else ⟦ y ⟧ᴺ ρ)
  if-semN true  x y ρ = refl
  if-semN false x y ρ = refl

  ltF-semN : ∀ a b x y ρ → ⟦ ltF a b x y ⟧ᴺ ρ ≡ (if ⟦ a ⟧ᴺ ρ <ᵇ ⟦ b ⟧ᴺ ρ then ⟦ x ⟧ᴺ ρ else ⟦ y ⟧ᴺ ρ)
  ltF-semN a b x y ρ with numOf a in ea | numOf b in eb
  ... | just u | just v rewrite numOf-eq a ea | numOf-eq b eb = if-semN (u <ᵇ v) x y ρ
  ... | just _ | nothing = refl
  ... | nothing | _ = refl

  if-cong : ∀ {a a′ b b′ : ℕ} {x x′ y y′ : ℕ} → a ≡ a′ → b ≡ b′ → x ≡ x′ → y ≡ y′ →
            (if a <ᵇ b then x else y) ≡ (if a′ <ᵇ b′ then x′ else y′)
  if-cong refl refl refl refl = refl

-- Shipping the folded discrete formula means what the symbolic coordinate means in ℕ.
encD-semN : ∀ (e : DExpr ℕ) (ρ : ℕ → ℕ) → ⟦ encD e ⟧ᴺ ρ ≡ evalD natD ρ e
encD-semN (pure v) ρ = refl
encD-semN (impure (inj₁ (inj₁ E.Zero) , _)) ρ = refl
encD-semN (impure (inj₁ (inj₁ (E.Lit n)) , _)) ρ = refl
encD-semN (impure (inj₁ (inj₁ E.Plus) , k)) ρ =
  trans (fold2-semN _+_ add (encD (k zero)) (encD (k (fsuc zero))) ρ refl) (cong₂ _+_ (encD-semN (k zero) ρ) (encD-semN (k (fsuc zero)) ρ))
encD-semN (impure (inj₁ (inj₁ E.Max) , k)) ρ =
  trans (fold2-semN _⊔_ max (encD (k zero)) (encD (k (fsuc zero))) ρ refl) (cong₂ _⊔_ (encD-semN (k zero) ρ) (encD-semN (k (fsuc zero)) ρ))
encD-semN (impure (inj₁ (inj₁ (E.Pct p)) , k)) ρ =
  trans (fold1-semN (λ x → (x * p) / 100) (pct p) (encD (k tt)) ρ refl) (cong (λ v → (v * p) / 100) (encD-semN (k tt) ρ))
encD-semN (impure (inj₁ (inj₂ E.Sub) , k)) ρ =
  trans (fold2-semN _∸_ sub (encD (k zero)) (encD (k (fsuc zero))) ρ refl) (cong₂ _∸_ (encD-semN (k zero) ρ) (encD-semN (k (fsuc zero)) ρ))
encD-semN (impure (inj₂ (Eu.DivBy d) , k)) ρ =
  trans (fold1-semN (λ x → x / suc d) (fdiv d) (encD (k tt)) ρ refl) (cong (λ v → v / suc d) (encD-semN (k tt) ρ))
encD-semN (impure (inj₂ (Eu.ModBy d) , k)) ρ =
  trans (fold1-semN (λ x → x % suc d) (fmod d) (encD (k tt)) ρ refl) (cong (λ v → v % suc d) (encD-semN (k tt) ρ))
encD-semN (impure (inj₂ (Eu.MulLit n) , k)) ρ =
  trans (fold1-semN (n *_) (fmul n) (encD (k tt)) ρ refl) (cong (n *_) (encD-semN (k tt) ρ))
encD-semN (impure (inj₂ Eu.Lt , k)) ρ =
  trans (ltF-semN (encD (k zero)) (encD (k (fsuc zero))) (encD (k (fsuc (fsuc zero)))) (encD (k (fsuc (fsuc (fsuc zero))))) ρ)
        (if-cong (encD-semN (k zero) ρ) (encD-semN (k (fsuc zero)) ρ)
                 (encD-semN (k (fsuc (fsuc zero))) ρ) (encD-semN (k (fsuc (fsuc (fsuc zero)))) ρ))

-- `half` is exact in the output reading
half-semN : ∀ f ρ → ⟦ half f ⟧ᴰ ρ ≡ (+ 1 ℚ./ 2) ℚ.* ι (⟦ f ⟧ᴺ ρ)
half-semN (num a) ρ with a % 2 ≟ 0
... | yes h = exactHalf a h
... | no _  = refl
half-semN (var _) ρ = refl
half-semN (add _ _) ρ = refl
half-semN (sub _ _) ρ = refl
half-semN (max _ _) ρ = refl
half-semN (pct _ _) ρ = refl
half-semN (hlf _) ρ = refl
half-semN (fdiv _ _) ρ = refl
half-semN (fmod _ _) ρ = refl
half-semN (fmul _ _) ρ = refl
half-semN (flt _ _ _ _) ρ = refl

------------------------------------------------------------------------
-- A folded number is the value of the discrete expression at every assignment

private
  fold1-inv : ∀ f mk → (∀ a m → mk a ≡ num m → ⊥) → ∀ a n → fold1 f mk a ≡ num n →
              ∃ λ x → a ≡ num x × f x ≡ n
  fold1-inv f mk nn a n h with numOf a in eq
  fold1-inv f mk nn a n refl | just x = x , numOf-eq a eq , refl
  fold1-inv f mk nn a n h    | nothing = ⊥-elim (nn a n h)

  fold2-inv : ∀ f mk → (∀ a b m → mk a b ≡ num m → ⊥) → ∀ a b n → fold2 f mk a b ≡ num n →
              ∃₂ λ x y → a ≡ num x × b ≡ num y × f x y ≡ n
  fold2-inv f mk nn a b n h with numOf a in ea | numOf b in eb
  fold2-inv f mk nn a b n refl | just x | just y = x , y , numOf-eq a ea , numOf-eq b eb , refl
  fold2-inv f mk nn a b n h    | just _ | nothing = ⊥-elim (nn a b n h)
  fold2-inv f mk nn a b n h    | nothing | _ = ⊥-elim (nn a b n h)

  ltF-inv : ∀ a b x y n → ltF a b x y ≡ num n →
            ∃₂ λ u v → a ≡ num u × b ≡ num v × (if u <ᵇ v then x else y) ≡ num n
  ltF-inv a b x y n h with numOf a in ea | numOf b in eb
  ltF-inv a b x y n h  | just u | just v = u , v , numOf-eq a ea , numOf-eq b eb , h
  ltF-inv a b x y n () | just _ | nothing
  ltF-inv a b x y n () | nothing | _

  no-add : ∀ a b m → add a b ≡ num m → ⊥
  no-add _ _ _ ()
  no-sub : ∀ a b m → sub a b ≡ num m → ⊥
  no-sub _ _ _ ()
  no-max : ∀ a b m → max a b ≡ num m → ⊥
  no-max _ _ _ ()

enc-numN : ∀ (e : DExpr ℕ) n → encD e ≡ num n → ∀ (ρ : ℕ → ℕ) → evalD natD ρ e ≡ n
enc-numN (pure v) n () ρ
enc-numN (impure (inj₁ (inj₁ E.Zero) , _)) n refl ρ = refl
enc-numN (impure (inj₁ (inj₁ (E.Lit m)) , _)) n refl ρ = refl
enc-numN (impure (inj₁ (inj₁ E.Plus) , k)) n h ρ with fold2-inv _+_ add no-add (encD (k zero)) (encD (k (fsuc zero))) n h
... | x , y , e₁ , e₂ , refl = cong₂ _+_ (enc-numN (k zero) x e₁ ρ) (enc-numN (k (fsuc zero)) y e₂ ρ)
enc-numN (impure (inj₁ (inj₁ E.Max) , k)) n h ρ with fold2-inv _⊔_ max no-max (encD (k zero)) (encD (k (fsuc zero))) n h
... | x , y , e₁ , e₂ , refl = cong₂ _⊔_ (enc-numN (k zero) x e₁ ρ) (enc-numN (k (fsuc zero)) y e₂ ρ)
enc-numN (impure (inj₁ (inj₁ (E.Pct p)) , k)) n h ρ with fold1-inv (λ x → (x * p) / 100) (pct p) (λ _ _ ()) (encD (k tt)) n h
... | x , e₁ , refl = cong (λ v → (v * p) / 100) (enc-numN (k tt) x e₁ ρ)
enc-numN (impure (inj₁ (inj₂ E.Sub) , k)) n h ρ with fold2-inv _∸_ sub no-sub (encD (k zero)) (encD (k (fsuc zero))) n h
... | x , y , e₁ , e₂ , refl = cong₂ _∸_ (enc-numN (k zero) x e₁ ρ) (enc-numN (k (fsuc zero)) y e₂ ρ)
enc-numN (impure (inj₂ (Eu.DivBy d) , k)) n h ρ with fold1-inv (λ x → x / suc d) (fdiv d) (λ _ _ ()) (encD (k tt)) n h
... | x , e₁ , refl = cong (λ v → v / suc d) (enc-numN (k tt) x e₁ ρ)
enc-numN (impure (inj₂ (Eu.ModBy d) , k)) n h ρ with fold1-inv (λ x → x % suc d) (fmod d) (λ _ _ ()) (encD (k tt)) n h
... | x , e₁ , refl = cong (λ v → v % suc d) (enc-numN (k tt) x e₁ ρ)
enc-numN (impure (inj₂ (Eu.MulLit m) , k)) n h ρ with fold1-inv (m *_) (fmul m) (λ _ _ ()) (encD (k tt)) n h
... | x , e₁ , refl = cong (m *_) (enc-numN (k tt) x e₁ ρ)
enc-numN (impure (inj₂ Eu.Lt , k)) n h ρ with ltF-inv (encD (k zero)) (encD (k (fsuc zero))) (encD (k (fsuc (fsuc zero)))) (encD (k (fsuc (fsuc (fsuc zero))))) n h
... | u , v , ea , eb , hh = trans cmp (pick (u <ᵇ v) hh)
  where
    cmp : (if evalD natD ρ (k zero) <ᵇ evalD natD ρ (k (fsuc zero))
           then evalD natD ρ (k (fsuc (fsuc zero))) else evalD natD ρ (k (fsuc (fsuc (fsuc zero)))))
          ≡ (if u <ᵇ v then evalD natD ρ (k (fsuc (fsuc zero))) else evalD natD ρ (k (fsuc (fsuc (fsuc zero)))))
    cmp = cong (λ c → if c then evalD natD ρ (k (fsuc (fsuc zero))) else evalD natD ρ (k (fsuc (fsuc (fsuc zero)))))
               (cong₂ _<ᵇ_ (enc-numN (k zero) u ea ρ) (enc-numN (k (fsuc zero)) v eb ρ))
    pick : ∀ c → (if c then encD (k (fsuc (fsuc zero))) else encD (k (fsuc (fsuc (fsuc zero))))) ≡ num n →
           (if c then evalD natD ρ (k (fsuc (fsuc zero))) else evalD natD ρ (k (fsuc (fsuc (fsuc zero))))) ≡ n
    pick true  hh′ = enc-numN (k (fsuc (fsuc zero))) n hh′ ρ
    pick false hh′ = enc-numN (k (fsuc (fsuc (fsuc zero)))) n hh′ ρ
