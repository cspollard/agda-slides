{-# OPTIONS --safe --without-K #-}

-- ℕ against ℚ along `ι`, for the layers the ℕ tick clock reads (core, Sub, Ord, Floor): which
-- operations are homomorphisms (Ord and Floor unconditionally; Sub needs `b ≤ a`, Pct exactness, or
-- the lowering `ι-monus`, `ι-pct`), and the laws of the ℚ model (`ratQLaws`).
module Slides.Diagram.Ordered.Properties where

open import Data.Bool using (Bool; true; false; not; if_then_else_; T)
open import Data.Integer as ℤ using (ℤ; +_)
import Data.Integer.DivMod as ℤ
open import Data.Integer.DivMod using (div-pos-is-/ℕ)
import Data.Integer.Properties as ℤP
open import Data.Integer.Tactic.RingSolver using (solve-∀)
open import Data.Nat as ℕ using (ℕ; suc; _*_; _∸_; _/_; _%_)
import Data.Nat.DivMod as ℕDM
import Data.Nat.Coprimality as ℕC
import Data.Nat.Divisibility as ℕD
import Data.Nat.Properties as ℕP
open import Data.Rational as ℚ using (ℚ)
open import Data.Product using (_,_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Unnormalised using (*≡*)
import Data.Rational.Unnormalised.Properties as ℚᵘP
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Slides.Diagram.NatQ
open import Slides.Diagram.NatQ.Properties
open import Slides.Diagram.Ordered

-- `ι` preserves multiplication
ι-* : ∀ a b → ι (a * b) ≡ ι a ℚ.* ι b
ι-* a b = ℚP.toℚᵘ-injective
  (ℚᵘP.≃-trans (toℚᵘ-ι (a * b))
  (ℚᵘP.≃-trans (*≡* (cong (ℤ._* + 1) (ℤP.pos-* a b)))
  (ℚᵘP.≃-sym (ℚᵘP.≃-trans (ℚP.toℚᵘ-homo-* (ι a) (ι b)) (ℚᵘP.*-cong (toℚᵘ-ι a) (toℚᵘ-ι b))))))

------------------------------------------------------------------------
-- `ι` and the order

-- the strict comparison of the naturals is the negation of the flipped `≤ᵇ`
private
  lt-aux : ∀ a b → (a ℕ.<ᵇ b) ≡ not (b ℕ.<ᵇ suc a)
  lt-aux ℕ.zero    ℕ.zero    = refl
  lt-aux ℕ.zero    (suc b)   = refl
  lt-aux (suc a)   ℕ.zero    = refl
  lt-aux (suc a)   (suc b)   = lt-aux a b

  le-aux : ∀ a b → (a ℕ.≤ᵇ b) ≡ (a ℕ.<ᵇ suc b)
  le-aux ℕ.zero    b = refl
  le-aux (suc a)   b = refl

nat-<ᵇ : ∀ a b → (a ℕ.<ᵇ b) ≡ not (b ℕ.≤ᵇ a)
nat-<ᵇ a b = trans (lt-aux a b) (cong not (sym (le-aux b a)))

ι-<ᵇ : ∀ a b → (ι a <ᵇℚ ι b) ≡ (a ℕ.<ᵇ b)
ι-<ᵇ a b = trans (cong not (ι-≤ᵇ b a)) (sym (nat-<ᵇ a b))

private
  ι-≤ : ∀ a b → (a ℕ.≤ᵇ b) ≡ true → ι a ℚ.≤ ι b
  ι-≤ a b eq = ℚP.≤ᵇ⇒≤ {ι a} {ι b} (subst T (sym (trans (ι-≤ᵇ a b) eq)) _)

  ι-≰ : ∀ a b → (a ℕ.≤ᵇ b) ≡ false → ι b ℚ.≤ ι a
  ι-≰ a b eq = ℚP.<⇒≤ (ℚP.≰⇒> (λ h → subst T (trans (ι-≤ᵇ a b) eq) (ℚP.≤⇒≤ᵇ {ι a} {ι b} h)))

ι-⊓ : ∀ a b → ι (a ℕ.⊓ b) ≡ ι a ℚ.⊓ ι b
ι-⊓ a b with a ℕ.≤ᵇ b in eq
... | true  = trans (cong ι (ℕP.m≤n⇒m⊓n≡m (ℕP.≤ᵇ⇒≤ a b (subst T (sym eq) _))))
                    (sym (ℚP.p≤q⇒p⊓q≡p (ι-≤ a b eq)))
... | false = trans (cong ι (ℕP.m≥n⇒m⊓n≡n (ℕP.≰⇒≥ (λ (h : a ℕ.≤ b) → subst T eq (ℕP.≤⇒≤ᵇ h)))))
                    (sym (ℚP.p≥q⇒p⊓q≡q (ι-≰ a b eq)))

------------------------------------------------------------------------
-- `ι` and the quotient

private
  coprime-1 : ∀ n → ℕC.Coprime n 1
  coprime-1 n (_ , d∣1) = ℕD.∣1⇒≡1 d∣1

  ι-mk : ∀ n → ι n ≡ ℚ.mkℚ (+ n) 0 (coprime-1 n)
  ι-mk n = ℚP.normalize-coprime (coprime-1 n)

-- the floor of a whole number is itself
floor-ι : ∀ n → ℚ.floor (ι n) ≡ + n
floor-ι n rewrite ι-mk n =
  trans (div-pos-is-/ℕ (+ n) 1) (cong +_ (ℕDM.n/1≡n n))

qdiv : ∀ a d → (+ a ℤ./ + suc d) ≡ + (a / suc d)
qdiv a d = div-pos-is-/ℕ (+ a) (suc d)

ι-divBy : ∀ d a → ι (a / suc d) ≡ FloorOps.divBy ratFloor d (ι a)
ι-divBy d a rewrite floor-ι a | qdiv a d = refl

ι-mulLit : ∀ n a → ι (n * a) ≡ FloorOps.mulLit ratFloor n (ι a)
ι-mulLit = ι-*

ι-modBy : ∀ d a → ι (a % suc d) ≡ FloorOps.modBy ratFloor d (ι a)
ι-modBy d a rewrite floor-ι a | qdiv a d =
  trans (cong ι (trans (ℕDM.m%n≡m∸m/n*n a (suc d)) (cong (a ∸_) (ℕP.*-comm (a / suc d) (suc d)))))
 (trans (ι-∸ a (suc d * (a / suc d)) (subst (λ x → x ℕ.≤ a) (ℕP.*-comm (a / suc d) (suc d)) (ℕDM.m/n*n≤m a (suc d))))
        (cong (λ y → ι a ℚ.- y) (ι-* (suc d) (a / suc d))))

------------------------------------------------------------------------
-- Which operations are homomorphisms of `ι`

record IsOrdHom {S T : Set} (O : OrdOps S) (P : OrdOps T) (h : S → T) : Set where
  private module O = OrdOps O
  private module P = OrdOps P
  field
    h-lt  : ∀ a b x y → h (O.lt a b x y) ≡ P.lt (h a) (h b) (h x) (h y)
    h-min : ∀ a b → h (O.min a b) ≡ P.min (h a) (h b)

record IsFloorHom {S T : Set} (O : FloorOps S) (P : FloorOps T) (h : S → T) : Set where
  private module O = FloorOps O
  private module P = FloorOps P
  field
    h-divBy  : ∀ d a → h (O.divBy d a) ≡ P.divBy d (h a)
    h-modBy  : ∀ d a → h (O.modBy d a) ≡ P.modBy d (h a)
    h-mulLit : ∀ n a → h (O.mulLit n a) ≡ P.mulLit n (h a)

-- `ι` is a homomorphism of the ordered layer, unconditionally
ι-ord : IsOrdHom natOrd ratOrd ι
ι-ord = record { h-lt = lt ; h-min = ι-⊓ }
  where lt : ∀ a b x y → ι (if a ℕ.<ᵇ b then x else y) ≡ (if ι a <ᵇℚ ι b then ι x else ι y)
        lt a b x y rewrite ι-<ᵇ a b with a ℕ.<ᵇ b
        ... | true  = refl
        ... | false = refl

-- and of the floor layer, unconditionally
ι-floor : IsFloorHom natFloor ratFloor ι
ι-floor = record { h-divBy = ι-divBy′ ; h-modBy = ι-modBy ; h-mulLit = ι-mulLit }
  where ι-divBy′ = λ d a → ι-divBy d a

------------------------------------------------------------------------
-- The monus and the percentage, as the lowering reads them

-- `a ∸ b` is `(a ⊔ b) − b` with no side condition (the minuend is the larger by construction)
ι-monus : ∀ a b → ι (a ∸ b) ≡ (ι a ℚ.⊔ ι b) ℚ.- ι b
ι-monus a b with b ℕ.≤ᵇ a in eq
... | true  = trans (ι-∸ a b (ℕP.≤ᵇ⇒≤ b a (subst T (sym eq) _)))
                    (cong (ℚ._- ι b) (sym (ℚP.p≥q⇒p⊔q≡p (ι-≤ b a eq))))
... | false = trans (cong ι (ℕP.m≤n⇒m∸n≡0 (ℕP.<⇒≤ (ℕP.≰⇒> (λ (h : b ℕ.≤ a) → subst T eq (ℕP.≤⇒≤ᵇ h))))))
                    (trans (sym (ℚP.+-inverseʳ (ι b)))
                           (cong (ℚ._- ι b) (sym (ℚP.p≤q⇒p⊔q≡q (ι-≰ b a eq)))))

-- `x·p/100` rounded down is the floor of `p·x/100` in ℚ
ι-pct : ∀ p x → ι ((x * p) / 100) ≡ FloorOps.divBy ratFloor 99 (FloorOps.mulLit ratFloor p (ι x))
ι-pct p x = trans (ι-divBy 99 (x * p)) (cong (FloorOps.divBy ratFloor 99) (trans (cong ι (ℕP.*-comm x p)) (ι-mulLit p x)))

------------------------------------------------------------------------
-- ℚ is a model of the laws

ratQLaws : QLaws ratO
ratQLaws = record { modBy-spec = λ _ _ → refl ; min-spec = min-lt }
  where
    min-lt : ∀ a b → a ℚ.⊓ b ≡ (if a <ᵇℚ b then a else b)
    min-lt a b with b ℚ.≤ᵇ a in eq
    ... | true  = ℚP.p≥q⇒p⊓q≡q (ℚP.≤ᵇ⇒≤ {b} {a} (subst T (sym eq) _))
    ... | false = ℚP.p≤q⇒p⊓q≡p (ℚP.<⇒≤ (ℚP.≰⇒> (λ h → subst T eq (ℚP.≤⇒≤ᵇ {b} {a} h))))
