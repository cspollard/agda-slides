{-# OPTIONS --safe --without-K #-}

-- What the shipped formulas mean (`Slides.Anim.Formula` defines them and the encoder).
--
-- `⟦_⟧` is the meaning of a shipped formula in ℚ, the model `ratQ` of the ordered layers
-- (`Slides.Diagram.Ordered`): floor division, remainder, factor, comparison, minimum and easing
-- are the operations of that model.
--
--   * `enc-sem`: `⟦ enc e ⟧ ρ ≡ evalQ ratQ ρ e` for every assignment `ρ`: shipping the folded
--     formula means what the symbolic coordinate means in ℚ.  So the folds are exact.  One generic
--     lemma (`fold1-sem`, `fold2-sem`) says a fold is exact when its operation on whole numbers is
--     a `ι`-homomorphism, and one lemma per operation supplies that (`Ordered.Properties`).
--   * `half-sem`: `⟦ half f ⟧ ρ ≡ (1/2) · ⟦ f ⟧ ρ`.
--   * `enc-numO`: if `enc e` folded to the number `n`, then `e` evaluates to `n` in ℕ (`natO`) at
--     *every* assignment (the all-zero one in particular, which is where the page's base elements
--     are taken).  `fold1-inv`, `fold2-inv` are the generic inversions.
--
-- Not proved: that the page's `ev` computes `⟦_⟧` (it does so in floating point; checked by
-- `tests/browser/anim-ref.mjs`).

module Slides.Anim.Formula.Properties where

open import Data.Bool using (Bool; true; false; if_then_else_; T)
open import Data.Fin using (zero) renaming (suc to fsuc)
open import Data.Container.FreeMonad using (pure; impure)
open import Data.Integer as ℤ using (+_)
import Data.Integer.Properties as ℤP
open import Data.Integer.Tactic.RingSolver using (solve-∀)
open import Data.Nat as ℕ using (ℕ; suc; _*_; _/_; _%_; _≤ᵇ_; _<ᵇ_; _∸_; _+_; _⊔_; _⊓_; _≟_)
import Data.Nat.DivMod as ℕDM
import Data.Nat.Properties as ℕP
open import Data.Rational as ℚ using (ℚ)
import Data.Rational.Properties as ℚP
import Data.Rational.Unnormalised.Properties as ℚᵘP
open import Data.Rational.Unnormalised using (*≡*)
open import Data.Product using (_,_; _×_; ∃; ∃₂)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
import Data.Maybe.Properties as MP
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Slides.Cong using (cong₄)
import Slides.Diagram.Expr as E
open import Slides.Diagram.NatQ
open import Slides.Diagram.NatQ.Properties
open import Slides.Diagram.Ordered using (OExpr; QExpr; OrdOps; FloorOps; ratOrd; ratFloor; ratQ; evalQ; evalO; natO; weakenQ; Lt; Min; DivBy; ModBy; MulLit; Ease)
open import Slides.Diagram.Ordered.Properties using (ι-<ᵇ; ι-⊓; ι-divBy; ι-modBy; ι-mulLit; exact%)
open import Slides.Anim.Track using (progress)
open import Slides.Anim.Formula

-- the meaning in ℚ, given the parameters of the segments
⟦_⟧ : Formula → (ℕ → ℚ) → ℚ
⟦ num n ⟧       ρ = ι n
⟦ var i ⟧       ρ = ρ i
⟦ add a b ⟧     ρ = ⟦ a ⟧ ρ ℚ.+ ⟦ b ⟧ ρ
⟦ sub a b ⟧     ρ = ⟦ a ⟧ ρ ℚ.- ⟦ b ⟧ ρ
⟦ max a b ⟧     ρ = ⟦ a ⟧ ρ ℚ.⊔ ⟦ b ⟧ ρ
⟦ pct p a ⟧     ρ = (+ p ℚ./ 100) ℚ.* ⟦ a ⟧ ρ
⟦ hlf a ⟧       ρ = (+ 1 ℚ./ 2) ℚ.* ⟦ a ⟧ ρ
⟦ fdiv d a ⟧    ρ = FloorOps.divBy ratFloor d (⟦ a ⟧ ρ)
⟦ fmod d a ⟧    ρ = FloorOps.modBy ratFloor d (⟦ a ⟧ ρ)
⟦ fmul n a ⟧    ρ = FloorOps.mulLit ratFloor n (⟦ a ⟧ ρ)
⟦ flt a b x y ⟧ ρ = OrdOps.lt ratOrd (⟦ a ⟧ ρ) (⟦ b ⟧ ρ) (⟦ x ⟧ ρ) (⟦ y ⟧ ρ)
⟦ fmin a b ⟧    ρ = ⟦ a ⟧ ρ ℚ.⊓ ⟦ b ⟧ ρ
⟦ fease e a ⟧   ρ = progress e (⟦ a ⟧ ρ)

numOf-eq : ∀ f {n} → numOf f ≡ just n → f ≡ num n
numOf-eq (num m) refl = refl

------------------------------------------------------------------------
-- Folds: soundness and inversion, once

-- a bind that succeeds has succeeded in each part
>>=-just : ∀ {A B : Set} (m : Maybe A) {f : A → Maybe B} {n} → (m Maybe.>>= f) ≡ just n →
           ∃ λ x → m ≡ just x × f x ≡ just n
>>=-just (just x) h = x , refl , h

-- Soundness of a fold: it is exact when the operation on whole numbers is a homomorphism of `ι`
-- (where it is defined)
private
  foldOr-sem : ∀ m g ρ {r} → (∀ n → m ≡ just n → ι n ≡ r) → ⟦ g ⟧ ρ ≡ r → ⟦ foldOr m g ⟧ ρ ≡ r
  foldOr-sem (just n) g ρ hj hg = hj n refl
  foldOr-sem nothing  g ρ hj hg = hg

fold1-sem : ∀ f mk (g : ℚ → ℚ) a ρ → (∀ x y → f x ≡ just y → ι y ≡ g (ι x)) →
            ⟦ mk a ⟧ ρ ≡ g (⟦ a ⟧ ρ) → ⟦ fold1 f mk a ⟧ ρ ≡ g (⟦ a ⟧ ρ)
fold1-sem f mk g a ρ ex h = foldOr-sem (numOf a Maybe.>>= f) (mk a) ρ hj h
  where
    hj : ∀ n → (numOf a Maybe.>>= f) ≡ just n → ι n ≡ g (⟦ a ⟧ ρ)
    hj n e with >>=-just (numOf a) e
    ... | x , ea , ef rewrite numOf-eq a ea = ex x n ef

fold2-sem : ∀ f mk (g : ℚ → ℚ → ℚ) a b ρ → (∀ x y z → f x y ≡ just z → ι z ≡ g (ι x) (ι y)) →
            ⟦ mk a b ⟧ ρ ≡ g (⟦ a ⟧ ρ) (⟦ b ⟧ ρ) → ⟦ fold2 f mk a b ⟧ ρ ≡ g (⟦ a ⟧ ρ) (⟦ b ⟧ ρ)
fold2-sem f mk g a b ρ ex h = foldOr-sem (numOf a Maybe.>>= λ x → numOf b Maybe.>>= f x) (mk a b) ρ hj h
  where
    hj : ∀ n → (numOf a Maybe.>>= λ x → numOf b Maybe.>>= f x) ≡ just n → ι n ≡ g (⟦ a ⟧ ρ) (⟦ b ⟧ ρ)
    hj n e with >>=-just (numOf a) e
    ... | x , ea , e₁ with >>=-just (numOf b) e₁
    ...   | y , eb , ef rewrite numOf-eq a ea | numOf-eq b eb = ex x y n ef

-- a fold that produced a number was applied to numbers (the node `mk` is never a number)
private
  foldOr-inv : ∀ m g n → foldOr m g ≡ num n → (∀ n′ → g ≡ num n′ → ⊥) → m ≡ just n
  foldOr-inv (just k) g n refl _  = refl
  foldOr-inv nothing  g n h     nn = ⊥-elim (nn n h)

fold1-inv : ∀ f mk → (∀ a n → mk a ≡ num n → ⊥) → ∀ a n → fold1 f mk a ≡ num n →
            ∃ λ x → a ≡ num x × f x ≡ just n
fold1-inv f mk nn a n h with >>=-just (numOf a) (foldOr-inv _ (mk a) n h (λ n′ → nn a n′))
... | x , ea , ef = x , numOf-eq a ea , ef

fold2-inv : ∀ f mk → (∀ a b n → mk a b ≡ num n → ⊥) → ∀ a b n → fold2 f mk a b ≡ num n →
            ∃₂ λ x y → a ≡ num x × b ≡ num y × f x y ≡ just n
fold2-inv f mk nn a b n h with >>=-just (numOf a) (foldOr-inv _ (mk a b) n h (λ n′ → nn a b n′))
... | x , ea , e₁ with >>=-just (numOf b) e₁
...   | y , eb , ef = x , y , numOf-eq a ea , numOf-eq b eb , ef

exactIf-inv : ∀ c {m n} → exactIf c m ≡ just n → m ≡ n
exactIf-inv true refl = refl

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

private
  -- the operations on whole numbers that fold, against their meaning in ℚ
  exact-monus : ∀ a b z → exactIf (b ≤ᵇ a) (a ∸ b) ≡ just z → ι z ≡ ι a ℚ.- ι b
  exact-monus a b z h with b ≤ᵇ a in eq
  exact-monus a b z refl | true = ι-∸ a b (ℕP.≤ᵇ⇒≤ b a (subst T (sym eq) tt))

  exact-pct : ∀ p a z → exactIf ⌊ (a * p) % 100 ≟ 0 ⌋ ((a * p) / 100) ≡ just z → ι z ≡ (+ p ℚ./ 100) ℚ.* ι a
  exact-pct p a z h with (a * p) % 100 ≟ 0
  exact-pct p a z refl | yes e = exact% p a e

  exact-half : ∀ a z → exactIf ⌊ a % 2 ≟ 0 ⌋ (a / 2) ≡ just z → ι z ≡ (+ 1 ℚ./ 2) ℚ.* ι a
  exact-half a z h with a % 2 ≟ 0
  exact-half a z refl | yes e = exactHalf a e

plus-sem : ∀ a b ρ → ⟦ plus a b ⟧ ρ ≡ ⟦ a ⟧ ρ ℚ.+ ⟦ b ⟧ ρ
plus-sem a b ρ = fold2-sem _ add ℚ._+_ a b ρ (λ x y z → λ { refl → ι-+ x y }) refl

maxF-sem : ∀ a b ρ → ⟦ maxF a b ⟧ ρ ≡ ⟦ a ⟧ ρ ℚ.⊔ ⟦ b ⟧ ρ
maxF-sem a b ρ = fold2-sem _ max ℚ._⊔_ a b ρ (λ x y z → λ { refl → ι-⊔ x y }) refl

minF-sem : ∀ a b ρ → ⟦ minF a b ⟧ ρ ≡ ⟦ a ⟧ ρ ℚ.⊓ ⟦ b ⟧ ρ
minF-sem a b ρ = fold2-sem _ fmin ℚ._⊓_ a b ρ (λ x y z → λ { refl → ι-⊓ x y }) refl

monus-sem : ∀ a b ρ → ⟦ monus a b ⟧ ρ ≡ ⟦ a ⟧ ρ ℚ.- ⟦ b ⟧ ρ
monus-sem a b ρ = fold2-sem _ sub ℚ._-_ a b ρ exact-monus refl

percent-sem : ∀ p a ρ → ⟦ percent p a ⟧ ρ ≡ (+ p ℚ./ 100) ℚ.* ⟦ a ⟧ ρ
percent-sem p a ρ = fold1-sem _ (pct p) (λ x → (+ p ℚ./ 100) ℚ.* x) a ρ (exact-pct p) refl

half-sem : ∀ a ρ → ⟦ half a ⟧ ρ ≡ (+ 1 ℚ./ 2) ℚ.* ⟦ a ⟧ ρ
half-sem a ρ = fold1-sem _ hlf (λ x → (+ 1 ℚ./ 2) ℚ.* x) a ρ exact-half refl

divF-sem : ∀ d a ρ → ⟦ divF d a ⟧ ρ ≡ FloorOps.divBy ratFloor d (⟦ a ⟧ ρ)
divF-sem d a ρ = fold1-sem _ (fdiv d) (FloorOps.divBy ratFloor d) a ρ (λ x y → λ { refl → ι-divBy d x }) refl

modF-sem : ∀ d a ρ → ⟦ modF d a ⟧ ρ ≡ FloorOps.modBy ratFloor d (⟦ a ⟧ ρ)
modF-sem d a ρ = fold1-sem _ (fmod d) (FloorOps.modBy ratFloor d) a ρ (λ x y → λ { refl → ι-modBy d x }) refl

mulF-sem : ∀ n a ρ → ⟦ mulF n a ⟧ ρ ≡ FloorOps.mulLit ratFloor n (⟦ a ⟧ ρ)
mulF-sem n a ρ = fold1-sem _ (fmul n) (FloorOps.mulLit ratFloor n) a ρ (λ x y → λ { refl → ι-mulLit n x }) refl

ltF-sem : ∀ a b x y ρ → ⟦ ltF a b x y ⟧ ρ ≡ OrdOps.lt ratOrd (⟦ a ⟧ ρ) (⟦ b ⟧ ρ) (⟦ x ⟧ ρ) (⟦ y ⟧ ρ)
ltF-sem a b x y ρ with numOf a in ea | numOf b in eb
... | just u | just v rewrite numOf-eq a ea | numOf-eq b eb | ι-<ᵇ u v with u <ᵇ v
...   | true  = refl
...   | false = refl
ltF-sem a b x y ρ | just _ | nothing = refl
ltF-sem a b x y ρ | nothing | _ = refl

-- Shipping the folded formula means what the symbolic coordinate means in ℚ.
enc-sem : ∀ (e : QExpr ℕ) (ρ : ℕ → ℚ) → ⟦ enc e ⟧ ρ ≡ evalQ ratQ ρ e
enc-sem (pure v) ρ = refl
enc-sem (impure (inj₁ (inj₁ (inj₁ E.Zero)) , _)) ρ = refl
enc-sem (impure (inj₁ (inj₁ (inj₁ (E.Lit n))) , _)) ρ = refl
enc-sem (impure (inj₁ (inj₁ (inj₁ E.Plus)) , k)) ρ =
  trans (plus-sem (enc (k zero)) (enc (k (fsuc zero))) ρ) (cong₂ ℚ._+_ (enc-sem (k zero) ρ) (enc-sem (k (fsuc zero)) ρ))
enc-sem (impure (inj₁ (inj₁ (inj₁ E.Max)) , k)) ρ =
  trans (maxF-sem (enc (k zero)) (enc (k (fsuc zero))) ρ) (cong₂ ℚ._⊔_ (enc-sem (k zero) ρ) (enc-sem (k (fsuc zero)) ρ))
enc-sem (impure (inj₁ (inj₁ (inj₁ (E.Pct p))) , k)) ρ =
  trans (percent-sem p (enc (k tt)) ρ) (cong ((+ p ℚ./ 100) ℚ.*_) (enc-sem (k tt) ρ))
enc-sem (impure (inj₁ (inj₁ (inj₂ E.Sub)) , k)) ρ =
  trans (monus-sem (enc (k zero)) (enc (k (fsuc zero))) ρ) (cong₂ ℚ._-_ (enc-sem (k zero) ρ) (enc-sem (k (fsuc zero)) ρ))
enc-sem (impure (inj₁ (inj₂ (inj₁ Lt)) , k)) ρ =
  trans (ltF-sem (enc (k zero)) (enc (k (fsuc zero))) (enc (k (fsuc (fsuc zero)))) (enc (k (fsuc (fsuc (fsuc zero))))) ρ)
        (cong₄ (OrdOps.lt ratOrd) (enc-sem (k zero) ρ) (enc-sem (k (fsuc zero)) ρ)
               (enc-sem (k (fsuc (fsuc zero))) ρ) (enc-sem (k (fsuc (fsuc (fsuc zero)))) ρ))
enc-sem (impure (inj₁ (inj₂ (inj₁ Min)) , k)) ρ =
  trans (minF-sem (enc (k zero)) (enc (k (fsuc zero))) ρ) (cong₂ ℚ._⊓_ (enc-sem (k zero) ρ) (enc-sem (k (fsuc zero)) ρ))
enc-sem (impure (inj₁ (inj₂ (inj₂ (DivBy d))) , k)) ρ =
  trans (divF-sem d (enc (k tt)) ρ) (cong (FloorOps.divBy ratFloor d) (enc-sem (k tt) ρ))
enc-sem (impure (inj₁ (inj₂ (inj₂ (ModBy d))) , k)) ρ =
  trans (modF-sem d (enc (k tt)) ρ) (cong (FloorOps.modBy ratFloor d) (enc-sem (k tt) ρ))
enc-sem (impure (inj₁ (inj₂ (inj₂ (MulLit n))) , k)) ρ =
  trans (mulF-sem n (enc (k tt)) ρ) (cong (FloorOps.mulLit ratFloor n) (enc-sem (k tt) ρ))
enc-sem (impure (inj₂ (Ease e) , k)) ρ = cong (progress e) (enc-sem (k tt) ρ)

------------------------------------------------------------------------
-- A folded number is the value of the expression at every assignment, in ℕ

private
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
  no-min : ∀ a b m → fmin a b ≡ num m → ⊥
  no-min _ _ _ ()

  just-inj : ∀ {a b : ℕ} → just a ≡ just b → a ≡ b
  just-inj refl = refl

enc-numO : ∀ (e : OExpr ℕ) n → enc (weakenQ e) ≡ num n → ∀ (ρ : ℕ → ℕ) → evalO natO ρ e ≡ n
enc-numO (pure v) n () ρ
enc-numO (impure (inj₁ (inj₁ E.Zero) , _)) n refl ρ = refl
enc-numO (impure (inj₁ (inj₁ (E.Lit m)) , _)) n refl ρ = refl
enc-numO (impure (inj₁ (inj₁ E.Plus) , k)) n h ρ with fold2-inv _ add no-add _ _ n h
... | x , y , e₁ , e₂ , ef =
  trans (cong₂ _+_ (enc-numO (k zero) x e₁ ρ) (enc-numO (k (fsuc zero)) y e₂ ρ)) (just-inj ef)
enc-numO (impure (inj₁ (inj₁ E.Max) , k)) n h ρ with fold2-inv _ max no-max _ _ n h
... | x , y , e₁ , e₂ , ef =
  trans (cong₂ _⊔_ (enc-numO (k zero) x e₁ ρ) (enc-numO (k (fsuc zero)) y e₂ ρ)) (just-inj ef)
enc-numO (impure (inj₁ (inj₁ (E.Pct p)) , k)) n h ρ with fold1-inv _ (pct p) (λ _ _ ()) _ n h
... | x , e₁ , ef =
  trans (cong (λ v → (v * p) / 100) (enc-numO (k tt) x e₁ ρ)) (exactIf-inv _ ef)
enc-numO (impure (inj₁ (inj₂ E.Sub) , k)) n h ρ with fold2-inv _ sub no-sub _ _ n h
... | x , y , e₁ , e₂ , ef =
  trans (cong₂ _∸_ (enc-numO (k zero) x e₁ ρ) (enc-numO (k (fsuc zero)) y e₂ ρ)) (exactIf-inv _ ef)
enc-numO (impure (inj₂ (inj₁ Lt) , k)) n h ρ with ltF-inv _ _ _ _ n h
... | u , v , ea , eb , hh = trans cmp (pick (u <ᵇ v) hh)
  where
    cmp : (if evalO natO ρ (k zero) <ᵇ evalO natO ρ (k (fsuc zero)) then evalO natO ρ (k (fsuc (fsuc zero))) else evalO natO ρ (k (fsuc (fsuc (fsuc zero)))))
          ≡ (if u <ᵇ v then evalO natO ρ (k (fsuc (fsuc zero))) else evalO natO ρ (k (fsuc (fsuc (fsuc zero)))))
    cmp = cong (λ c → if c then evalO natO ρ (k (fsuc (fsuc zero))) else evalO natO ρ (k (fsuc (fsuc (fsuc zero)))))
               (cong₂ _<ᵇ_ (enc-numO (k zero) u ea ρ) (enc-numO (k (fsuc zero)) v eb ρ))
    pick : ∀ c → (if c then enc (weakenQ (k (fsuc (fsuc zero)))) else enc (weakenQ (k (fsuc (fsuc (fsuc zero)))))) ≡ num n →
           (if c then evalO natO ρ (k (fsuc (fsuc zero))) else evalO natO ρ (k (fsuc (fsuc (fsuc zero))))) ≡ n
    pick true  hh′ = enc-numO (k (fsuc (fsuc zero))) n hh′ ρ
    pick false hh′ = enc-numO (k (fsuc (fsuc (fsuc zero)))) n hh′ ρ
enc-numO (impure (inj₂ (inj₁ Min) , k)) n h ρ with fold2-inv _ fmin no-min _ _ n h
... | x , y , e₁ , e₂ , ef =
  trans (cong₂ _⊓_ (enc-numO (k zero) x e₁ ρ) (enc-numO (k (fsuc zero)) y e₂ ρ)) (just-inj ef)
enc-numO (impure (inj₂ (inj₂ (DivBy d)) , k)) n h ρ with fold1-inv _ (fdiv d) (λ _ _ ()) _ n h
... | x , e₁ , ef = trans (cong (_/ suc d) (enc-numO (k tt) x e₁ ρ)) (just-inj ef)
enc-numO (impure (inj₂ (inj₂ (ModBy d)) , k)) n h ρ with fold1-inv _ (fmod d) (λ _ _ ()) _ n h
... | x , e₁ , ef = trans (cong (_% suc d) (enc-numO (k tt) x e₁ ρ)) (just-inj ef)
enc-numO (impure (inj₂ (inj₂ (MulLit m)) , k)) n h ρ with fold1-inv _ (fmul m) (λ _ _ ()) _ n h
... | x , e₁ , ef = trans (cong (m *_) (enc-numO (k tt) x e₁ ρ)) (just-inj ef)

-- `half` of a number only folds when the number is even, and then to its half
half-num-inv : ∀ a n → half a ≡ num n → ∃ λ x → a ≡ num x × x / 2 ≡ n
half-num-inv a n h with fold1-inv _ hlf (λ _ _ ()) a n h
... | x , ea , ef = x , ea , exactIf-inv _ ef
