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
open import Slides.Diagram.Expr using (Expr; evalWith; eval)
open import Slides.Diagram.Euclid using (DExpr; evalD; natD)
import Slides.Diagram.Euclid as Eu
import Slides.Diagram.Expr as E
open import Slides.Diagram.Expr.Properties.Faithful using (exact%)
open import Slides.Diagram.NatQ
open import Slides.Diagram.NatQ.Properties
open import Slides.Diagram.Scalar using (ratOps)
open import Slides.Diagram.Ordered
open import Slides.Diagram.Ordered.Properties
open import Slides.Diagram.Ordered.Properties.Laws using (evalQ-weaken; evalO-weaken)
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

-- Soundness of a fold, for any reading `sem` of formulas whose reading of a number is `nm`: it is
-- exact when the operation on whole numbers is a homomorphism of `nm` (where it is defined)
foldOr-sem : ∀ {A : Set} (sem : Formula → A) (nm : ℕ → A) → (∀ n → sem (num n) ≡ nm n) →
             ∀ m g {r} → (∀ n → m ≡ just n → nm n ≡ r) → sem g ≡ r → sem (foldOr m g) ≡ r
foldOr-sem sem nm nl (just n) g hj hg = trans (nl n) (hj n refl)
foldOr-sem sem nm nl nothing  g hj hg = hg

fold1-sem : ∀ {A : Set} (sem : Formula → A) (nm : ℕ → A) → (∀ n → sem (num n) ≡ nm n) →
            ∀ f mk (g : A → A) a → (∀ x y → f x ≡ just y → nm y ≡ g (nm x)) →
            sem (mk a) ≡ g (sem a) → sem (fold1 f mk a) ≡ g (sem a)
fold1-sem sem nm nl f mk g a ex h = foldOr-sem sem nm nl (numOf a Maybe.>>= f) (mk a) hj h
  where
    hj : ∀ n → (numOf a Maybe.>>= f) ≡ just n → nm n ≡ g (sem a)
    hj n e with >>=-just (numOf a) e
    ... | x , ea , ef rewrite numOf-eq a ea = trans (ex x n ef) (cong g (sym (nl x)))

fold2-sem : ∀ {A : Set} (sem : Formula → A) (nm : ℕ → A) → (∀ n → sem (num n) ≡ nm n) →
            ∀ f mk (g : A → A → A) a b → (∀ x y z → f x y ≡ just z → nm z ≡ g (nm x) (nm y)) →
            sem (mk a b) ≡ g (sem a) (sem b) → sem (fold2 f mk a b) ≡ g (sem a) (sem b)
fold2-sem sem nm nl f mk g a b ex h = foldOr-sem sem nm nl (numOf a Maybe.>>= λ x → numOf b Maybe.>>= f x) (mk a b) hj h
  where
    hj : ∀ n → (numOf a Maybe.>>= λ x → numOf b Maybe.>>= f x) ≡ just n → nm n ≡ g (sem a) (sem b)
    hj n e with >>=-just (numOf a) e
    ... | x , ea , e₁ with >>=-just (numOf b) e₁
    ...   | y , eb , ef rewrite numOf-eq a ea | numOf-eq b eb = trans (ex x y n ef) (cong₂ g (sym (nl x)) (sym (nl y)))

private
  -- the same, at ℚ
  fold1ℚ : ∀ f mk (g : ℚ → ℚ) a ρ → (∀ x y → f x ≡ just y → ι y ≡ g (ι x)) →
           ⟦ mk a ⟧ ρ ≡ g (⟦ a ⟧ ρ) → ⟦ fold1 f mk a ⟧ ρ ≡ g (⟦ a ⟧ ρ)
  fold1ℚ f mk g a ρ = fold1-sem (λ x → ⟦ x ⟧ ρ) ι (λ _ → refl) f mk g a

  fold2ℚ : ∀ f mk (g : ℚ → ℚ → ℚ) a b ρ → (∀ x y z → f x y ≡ just z → ι z ≡ g (ι x) (ι y)) →
           ⟦ mk a b ⟧ ρ ≡ g (⟦ a ⟧ ρ) (⟦ b ⟧ ρ) → ⟦ fold2 f mk a b ⟧ ρ ≡ g (⟦ a ⟧ ρ) (⟦ b ⟧ ρ)
  fold2ℚ f mk g a b ρ = fold2-sem (λ x → ⟦ x ⟧ ρ) ι (λ _ → refl) f mk g a b

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
plus-sem a b ρ = fold2ℚ _ add ℚ._+_ a b ρ (λ x y z → λ { refl → ι-+ x y }) refl

maxF-sem : ∀ a b ρ → ⟦ maxF a b ⟧ ρ ≡ ⟦ a ⟧ ρ ℚ.⊔ ⟦ b ⟧ ρ
maxF-sem a b ρ = fold2ℚ _ max ℚ._⊔_ a b ρ (λ x y z → λ { refl → ι-⊔ x y }) refl

minF-sem : ∀ a b ρ → ⟦ minF a b ⟧ ρ ≡ ⟦ a ⟧ ρ ℚ.⊓ ⟦ b ⟧ ρ
minF-sem a b ρ = fold2ℚ _ fmin ℚ._⊓_ a b ρ (λ x y z → λ { refl → ι-⊓ x y }) refl

monus-sem : ∀ a b ρ → ⟦ monus a b ⟧ ρ ≡ ⟦ a ⟧ ρ ℚ.- ⟦ b ⟧ ρ
monus-sem a b ρ = fold2ℚ _ sub ℚ._-_ a b ρ exact-monus refl

percent-sem : ∀ p a ρ → ⟦ percent p a ⟧ ρ ≡ (+ p ℚ./ 100) ℚ.* ⟦ a ⟧ ρ
percent-sem p a ρ = fold1ℚ _ (pct p) (λ x → (+ p ℚ./ 100) ℚ.* x) a ρ (exact-pct p) refl

half-sem : ∀ a ρ → ⟦ half a ⟧ ρ ≡ (+ 1 ℚ./ 2) ℚ.* ⟦ a ⟧ ρ
half-sem a ρ = fold1ℚ _ hlf (λ x → (+ 1 ℚ./ 2) ℚ.* x) a ρ exact-half refl

divF-sem : ∀ d a ρ → ⟦ divF d a ⟧ ρ ≡ FloorOps.divBy ratFloor d (⟦ a ⟧ ρ)
divF-sem d a ρ = fold1ℚ _ (fdiv d) (FloorOps.divBy ratFloor d) a ρ (λ x y → λ { refl → ι-divBy d x }) refl

modF-sem : ∀ d a ρ → ⟦ modF d a ⟧ ρ ≡ FloorOps.modBy ratFloor d (⟦ a ⟧ ρ)
modF-sem d a ρ = fold1ℚ _ (fmod d) (FloorOps.modBy ratFloor d) a ρ (λ x y → λ { refl → ι-modBy d x }) refl

mulF-sem : ∀ n a ρ → ⟦ mulF n a ⟧ ρ ≡ FloorOps.mulLit ratFloor n (⟦ a ⟧ ρ)
mulF-sem n a ρ = fold1ℚ _ (fmul n) (FloorOps.mulLit ratFloor n) a ρ (λ x y → λ { refl → ι-mulLit n x }) refl

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

-- the same two facts for a continuous template (`Expr`), through its weakening
enc-semE : ∀ (e : Expr ℕ) (ρ : ℕ → ℚ) → ⟦ encE e ⟧ ρ ≡ evalWith ratOps ρ e
enc-semE e ρ = trans (enc-sem (weakenQ (weakenO e)) ρ) (trans (evalQ-weaken ratQ ρ (weakenO e)) (evalO-weaken ratO ρ e))

enc-numE : ∀ (e : Expr ℕ) n → encE e ≡ num n → ∀ (ρ : ℕ → ℕ) → eval ρ e ≡ n
enc-numE e n h ρ = trans (sym (evalO-weaken natO ρ e)) (enc-numO (weakenO e) n h ρ)

------------------------------------------------------------------------
-- Discrete templates: the same formulas, read in ℕ  (removed when the discrete mode is)
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
⟦ fmin a b ⟧ᴺ   ρ = ⟦ a ⟧ᴺ ρ ⊓ ⟦ b ⟧ᴺ ρ
⟦ fease e a ⟧ᴺ  ρ = ⟦ a ⟧ᴺ ρ           -- an easing has no ℕ reading; no discrete template has one

⟦_⟧ᴰ : Formula → (ℕ → ℕ) → ℚ
⟦ hlf a ⟧ᴰ ρ = (+ 1 ℚ./ 2) ℚ.* ι (⟦ a ⟧ᴺ ρ)
⟦ f ⟧ᴰ     ρ = ι (⟦ f ⟧ᴺ ρ)

private
  fold1N : ∀ f mk a ρ → ⟦ mk a ⟧ᴺ ρ ≡ f (⟦ a ⟧ᴺ ρ) → ⟦ fold1 (tot1 f) mk a ⟧ᴺ ρ ≡ f (⟦ a ⟧ᴺ ρ)
  fold1N f mk a ρ = fold1-sem (λ x → ⟦ x ⟧ᴺ ρ) (λ n → n) (λ _ → refl) (tot1 f) mk f a (λ x y h → sym (just-inj h))

  fold2N : ∀ f mk a b ρ → ⟦ mk a b ⟧ᴺ ρ ≡ f (⟦ a ⟧ᴺ ρ) (⟦ b ⟧ᴺ ρ) →
           ⟦ fold2 (tot2 f) mk a b ⟧ᴺ ρ ≡ f (⟦ a ⟧ᴺ ρ) (⟦ b ⟧ᴺ ρ)
  fold2N f mk a b ρ = fold2-sem (λ x → ⟦ x ⟧ᴺ ρ) (λ n → n) (λ _ → refl) (tot2 f) mk f a b (λ x y z h → sym (just-inj h))

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
  trans (fold2N _+_ add (encD (k zero)) (encD (k (fsuc zero))) ρ refl) (cong₂ _+_ (encD-semN (k zero) ρ) (encD-semN (k (fsuc zero)) ρ))
encD-semN (impure (inj₁ (inj₁ E.Max) , k)) ρ =
  trans (fold2N _⊔_ max (encD (k zero)) (encD (k (fsuc zero))) ρ refl) (cong₂ _⊔_ (encD-semN (k zero) ρ) (encD-semN (k (fsuc zero)) ρ))
encD-semN (impure (inj₁ (inj₁ (E.Pct p)) , k)) ρ =
  trans (fold1N (λ x → (x * p) / 100) (pct p) (encD (k tt)) ρ refl) (cong (λ v → (v * p) / 100) (encD-semN (k tt) ρ))
encD-semN (impure (inj₁ (inj₂ E.Sub) , k)) ρ =
  trans (fold2N _∸_ sub (encD (k zero)) (encD (k (fsuc zero))) ρ refl) (cong₂ _∸_ (encD-semN (k zero) ρ) (encD-semN (k (fsuc zero)) ρ))
encD-semN (impure (inj₂ (Eu.DivBy d) , k)) ρ =
  trans (fold1N (λ x → x / suc d) (fdiv d) (encD (k tt)) ρ refl) (cong (λ v → v / suc d) (encD-semN (k tt) ρ))
encD-semN (impure (inj₂ (Eu.ModBy d) , k)) ρ =
  trans (fold1N (λ x → x % suc d) (fmod d) (encD (k tt)) ρ refl) (cong (λ v → v % suc d) (encD-semN (k tt) ρ))
encD-semN (impure (inj₂ (Eu.MulLit n) , k)) ρ =
  trans (fold1N (n *_) (fmul n) (encD (k tt)) ρ refl) (cong (n *_) (encD-semN (k tt) ρ))
encD-semN (impure (inj₂ Eu.Lt , k)) ρ =
  trans (ltF-semN (encD (k zero)) (encD (k (fsuc zero))) (encD (k (fsuc (fsuc zero)))) (encD (k (fsuc (fsuc (fsuc zero))))) ρ)
        (if-cong (encD-semN (k zero) ρ) (encD-semN (k (fsuc zero)) ρ)
                 (encD-semN (k (fsuc (fsuc zero))) ρ) (encD-semN (k (fsuc (fsuc (fsuc zero)))) ρ))

-- `half` is exact in the output reading
half-semN : ∀ f ρ → ⟦ half f ⟧ᴰ ρ ≡ (+ 1 ℚ./ 2) ℚ.* ι (⟦ f ⟧ᴺ ρ)
half-semN f ρ = foldOr-sem (λ x → ⟦ x ⟧ᴰ ρ) ι (λ _ → refl) _ (hlf f) hj refl
  where
    hj : ∀ n → (numOf f Maybe.>>= λ a → exactIf ⌊ a % 2 ≟ 0 ⌋ (a / 2)) ≡ just n → ι n ≡ (+ 1 ℚ./ 2) ℚ.* ι (⟦ f ⟧ᴺ ρ)
    hj n e with >>=-just (numOf f) e
    ... | x , ef , eh rewrite numOf-eq f ef = exact-half x n eh

-- A folded number is the value of the discrete expression at every assignment
enc-numN : ∀ (e : DExpr ℕ) n → encD e ≡ num n → ∀ (ρ : ℕ → ℕ) → evalD natD ρ e ≡ n
enc-numN (pure v) n () ρ
enc-numN (impure (inj₁ (inj₁ E.Zero) , _)) n refl ρ = refl
enc-numN (impure (inj₁ (inj₁ (E.Lit m)) , _)) n refl ρ = refl
enc-numN (impure (inj₁ (inj₁ E.Plus) , k)) n h ρ with fold2-inv _ add no-add _ _ n h
... | x , y , e₁ , e₂ , ef = trans (cong₂ _+_ (enc-numN (k zero) x e₁ ρ) (enc-numN (k (fsuc zero)) y e₂ ρ)) (just-inj ef)
enc-numN (impure (inj₁ (inj₁ E.Max) , k)) n h ρ with fold2-inv _ max no-max _ _ n h
... | x , y , e₁ , e₂ , ef = trans (cong₂ _⊔_ (enc-numN (k zero) x e₁ ρ) (enc-numN (k (fsuc zero)) y e₂ ρ)) (just-inj ef)
enc-numN (impure (inj₁ (inj₁ (E.Pct p)) , k)) n h ρ with fold1-inv _ (pct p) (λ _ _ ()) _ n h
... | x , e₁ , ef = trans (cong (λ v → (v * p) / 100) (enc-numN (k tt) x e₁ ρ)) (just-inj ef)
enc-numN (impure (inj₁ (inj₂ E.Sub) , k)) n h ρ with fold2-inv _ sub no-sub _ _ n h
... | x , y , e₁ , e₂ , ef = trans (cong₂ _∸_ (enc-numN (k zero) x e₁ ρ) (enc-numN (k (fsuc zero)) y e₂ ρ)) (just-inj ef)
enc-numN (impure (inj₂ (Eu.DivBy d) , k)) n h ρ with fold1-inv _ (fdiv d) (λ _ _ ()) _ n h
... | x , e₁ , ef = trans (cong (λ v → v / suc d) (enc-numN (k tt) x e₁ ρ)) (just-inj ef)
enc-numN (impure (inj₂ (Eu.ModBy d) , k)) n h ρ with fold1-inv _ (fmod d) (λ _ _ ()) _ n h
... | x , e₁ , ef = trans (cong (λ v → v % suc d) (enc-numN (k tt) x e₁ ρ)) (just-inj ef)
enc-numN (impure (inj₂ (Eu.MulLit m) , k)) n h ρ with fold1-inv _ (fmul m) (λ _ _ ()) _ n h
... | x , e₁ , ef = trans (cong (m *_) (enc-numN (k tt) x e₁ ρ)) (just-inj ef)
enc-numN (impure (inj₂ Eu.Lt , k)) n h ρ with ltF-inv _ _ _ _ n h
... | u , v , ea , eb , hh = trans cmp (pick (u <ᵇ v) hh)
  where
    cmp : (if evalD natD ρ (k zero) <ᵇ evalD natD ρ (k (fsuc zero)) then evalD natD ρ (k (fsuc (fsuc zero))) else evalD natD ρ (k (fsuc (fsuc (fsuc zero)))))
          ≡ (if u <ᵇ v then evalD natD ρ (k (fsuc (fsuc zero))) else evalD natD ρ (k (fsuc (fsuc (fsuc zero)))))
    cmp = cong (λ c → if c then evalD natD ρ (k (fsuc (fsuc zero))) else evalD natD ρ (k (fsuc (fsuc (fsuc zero)))))
               (cong₂ _<ᵇ_ (enc-numN (k zero) u ea ρ) (enc-numN (k (fsuc zero)) v eb ρ))
    pick : ∀ c → (if c then encD (k (fsuc (fsuc zero))) else encD (k (fsuc (fsuc (fsuc zero))))) ≡ num n → (if c then evalD natD ρ (k (fsuc (fsuc zero))) else evalD natD ρ (k (fsuc (fsuc (fsuc zero))))) ≡ n
    pick true  hh′ = enc-numN (k (fsuc (fsuc zero))) n hh′ ρ
    pick false hh′ = enc-numN (k (fsuc (fsuc (fsuc zero)))) n hh′ ρ
