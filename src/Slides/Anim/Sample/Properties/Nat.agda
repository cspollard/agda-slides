{-# OPTIONS --safe --without-K #-}

-- THEORY MODULE.  The reading of scenes in the ℕ clock, at a whole tick (`Slides.Time.Nat`: every
-- law of the clock is arithmetic).
--
--   seq-left, seq-right   `Seq` reads its first operand before its end, and the second one shifted after it
--   hold-in               a window shows its operand inside it
--   loop-tick             `Repeat n` at tick `k * d + τ` (`k < n`, `τ < d`) shows its operand at tick `τ`
--
-- `Slides.Input.Slides.Properties.Scene` reads a deck with them.

module Slides.Anim.Sample.Properties.Nat where

open import Data.Bool.Base using (true; false; T)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; _<ᵇ_; s≤s)
open import Data.Nat.Properties using (+-assoc; +-comm; +-monoʳ-<; <⇒<ᵇ; <ᵇ⇒<; m+n∸m≡n; m≤m+n; <⇒≱; <-≤-trans; *-monoˡ-≤)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; trans; sym; subst)

open import Slides.Anim.Sample using (TM; seqW; holdT; loopT)
open import Slides.Time.Nat using (natClock)

lt-true : ∀ {m n} → m < n → (m <ᵇ n) ≡ true
lt-true {m} {n} m<n with m <ᵇ n in e | <⇒<ᵇ m<n
... | true  | _ = refl

lt-false : ∀ {m n} → n ≤ m → (m <ᵇ n) ≡ false
lt-false {m} {n} n≤m with m <ᵇ n in e
... | false = refl
... | true  = ⊥-elim (<⇒≱ (<ᵇ⇒< m n (subst T (sym e) tt)) n≤m)

module _ {X : Set} where

  seq-left : ∀ (x y : TM natClock X) j → j < proj₁ x → proj₂ (seqW natClock x y) j ≡ proj₂ x j
  seq-left (n , f) (m , g) j lt rewrite lt-true lt | lt-true (<-≤-trans lt (m≤m+n n m)) = refl

  seq-right : ∀ (x y : TM natClock X) a → a < proj₁ y → proj₂ (seqW natClock x y) (proj₁ x + a) ≡ proj₂ y a
  seq-right (n , f) (m , g) a lt rewrite lt-true (+-monoʳ-< n lt) | lt-false (m≤m+n n a) | m+n∸m≡n n a = refl

  hold-in : ∀ d (x : TM natClock X) j → j < d → proj₂ (holdT natClock d x) j ≡ proj₂ x j
  hold-in d x j lt rewrite lt-true lt = refl

  loop-dur : ∀ n (x : TM natClock X) → proj₁ (loopT natClock n x) ≡ n * proj₁ x
  loop-dur zero    x = refl
  loop-dur (suc n) x = cong (proj₁ x +_) (loop-dur n x)

  loop-tick : ∀ n k τ (x : TM natClock X) → k < n → τ < proj₁ x →
              proj₂ (loopT natClock n x) (k * proj₁ x + τ) ≡ proj₂ x τ
  loop-tick (suc n) zero    τ x _ lt = seq-left x (loopT natClock n x) τ lt
  loop-tick (suc n) (suc k) τ x (s≤s k<n) lt =
    trans (cong (proj₂ (loopT natClock (suc n) x)) (+-assoc (proj₁ x) (k * proj₁ x) τ))
    (trans (seq-right x (loopT natClock n x) (k * proj₁ x + τ) bound)
           (loop-tick n k τ x k<n lt))
    where
      bound : k * proj₁ x + τ < proj₁ (loopT natClock n x)
      bound = subst (k * proj₁ x + τ <_) (sym (loop-dur n x))
                (<-≤-trans (+-monoʳ-< (k * proj₁ x) lt)
                  (subst (_≤ n * proj₁ x) (+-comm (proj₁ x) (k * proj₁ x)) (*-monoˡ-≤ (proj₁ x) k<n)))
