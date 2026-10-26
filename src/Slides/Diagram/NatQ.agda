{-# OPTIONS --safe --without-K #-}

-- The naturals inside the rationals: `ι n = n/1`, which is `fromℕ` of `ratOps`.
--
-- Everything is proved through `ℚᵘ` (unreduced fractions), where the arithmetic computes:
-- `toℚᵘ (ι n) ≃ mkℚᵘ (+ n) 0`, and `toℚᵘ` is an injective homomorphism.  What is shown is
-- what the comparison of the discrete (ℕ) and the continuous (ℚ) frames needs
-- (`Slides.Anim.Continuous`): `ι` preserves `+`, `⊔`, `≤` (as a boolean) and the exact
-- case of `∸`, and `ι t · (1/d) = t/d`.

module Slides.Diagram.NatQ where

open import Data.Bool using (Bool; true; false)
open import Data.Integer as ℤ using (ℤ; +_)
open import Data.Product using (_,_)
open import Data.Integer.Tactic.RingSolver using (solve-∀)
import Data.Integer.Properties as ℤP
open import Data.Nat as ℕ using (ℕ; suc)
import Data.Nat.Coprimality as ℕC
import Data.Nat.Divisibility as ℕD
import Data.Nat.Properties as ℕP
open import Data.Rational as ℚ using (ℚ; _/_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Unnormalised as ℚᵘ using (ℚᵘ; mkℚᵘ; *≡*; *≤*; _≃_)
import Data.Rational.Unnormalised.Properties as ℚᵘP
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Bool using (T; if_then_else_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

ι : ℕ → ℚ
ι n = + n / 1

-- `toℚᵘ (ι n)` is the fraction `n/1`
toℚᵘ-ι : ∀ n → ℚ.toℚᵘ (ι n) ℚᵘ.≃ mkℚᵘ (+ n) 0
toℚᵘ-ι n = ℚP.toℚᵘ-fromℚᵘ (mkℚᵘ (+ n) 0)

toℚᵘ-/ : ∀ n d′ → ℚ.toℚᵘ (n / suc d′) ℚᵘ.≃ mkℚᵘ n d′
toℚᵘ-/ n d′ = ℚP.toℚᵘ-fromℚᵘ (mkℚᵘ n d′)

private
  lem-+ : ∀ x y → (x ℤ.+ y) ℤ.* + 1 ≡ (x ℤ.* + 1 ℤ.+ y ℤ.* + 1) ℤ.* + 1
  lem-+ = solve-∀

ι-+ : ∀ a b → ι (a ℕ.+ b) ≡ ι a ℚ.+ ι b
ι-+ a b = ℚP.toℚᵘ-injective
  (ℚᵘP.≃-trans (toℚᵘ-ι (a ℕ.+ b))
  (ℚᵘP.≃-trans (*≡* (trans (cong (ℤ._* + 1) (ℤP.pos-+ a b)) (lem-+ (+ a) (+ b))))
  (ℚᵘP.≃-sym (ℚᵘP.≃-trans (ℚP.toℚᵘ-homo-+ (ι a) (ι b)) (ℚᵘP.+-cong (toℚᵘ-ι a) (toℚᵘ-ι b))))))

-- comparison: `ι` reflects and preserves `≤ᵇ`
private
  coprime-1 : ∀ n → ℕC.Coprime n 1
  coprime-1 n (_ , d∣1) = ℕD.∣1⇒≡1 d∣1

  ι-mk : ∀ n → ι n ≡ ℚ.mkℚ (+ n) 0 (coprime-1 n)
  ι-mk n = ℚP.normalize-coprime (coprime-1 n)

ι-≤ᵇ : ∀ a b → (ι a ℚ.≤ᵇ ι b) ≡ (a ℕ.≤ᵇ b)
ι-≤ᵇ a b rewrite ι-mk a | ι-mk b | ℕP.*-identityʳ a | ℕP.*-identityʳ b | ℤP.+◃n≡+n a | ℤP.+◃n≡+n b = refl

-- maximum
private
  ι-≤ : ∀ a b → (a ℕ.≤ᵇ b) ≡ true → ι a ℚ.≤ ι b
  ι-≤ a b eq = ℚP.≤ᵇ⇒≤ {ι a} {ι b} (subst T (sym (trans (ι-≤ᵇ a b) eq)) tt)

  ι-≰ : ∀ a b → (a ℕ.≤ᵇ b) ≡ false → ι b ℚ.≤ ι a
  ι-≰ a b eq = ℚP.<⇒≤ (ℚP.≰⇒> (λ h → subst T (trans (ι-≤ᵇ a b) eq) (ℚP.≤⇒≤ᵇ {ι a} {ι b} h)))

ι-⊔ : ∀ a b → ι (a ℕ.⊔ b) ≡ ι a ℚ.⊔ ι b
ι-⊔ a b with a ℕ.≤ᵇ b in eq
... | true  = trans (cong ι (ℕP.m≤n⇒m⊔n≡n (ℕP.≤ᵇ⇒≤ a b (subst T (sym eq) tt))))
                    (sym (ℚP.p≤q⇒p⊔q≡q (ι-≤ a b eq)))
... | false = trans (cong ι (ℕP.m≥n⇒m⊔n≡m (ℕP.≰⇒≥ (λ (h : a ℕ.≤ b) → subst T eq (ℕP.≤⇒≤ᵇ h)))))
                    (sym (ℚP.p≥q⇒p⊔q≡p (ι-≰ a b eq)))

-- difference: exact where the minuend is the larger (the monus is not the difference otherwise)
private
  pos∸ : ∀ a b → b ℕ.≤ a → + (a ℕ.∸ b) ≡ + a ℤ.- + b
  pos∸ a b h = trans (sym (ℤP.⊖-≥ h)) (sym (ℤP.m-n≡m⊖n a b))

  lem-- : ∀ x y → (x ℤ.- y) ℤ.* + 1 ≡ (x ℤ.* + 1 ℤ.+ (ℤ.- y) ℤ.* + 1) ℤ.* + 1
  lem-- = solve-∀

  ratio-eq : ∀ t d′ → + t ℤ.* + 1 ℤ.* + suc d′ ≡ + t ℤ.* + suc (d′ ℕ.+ 0)
  ratio-eq t d′ rewrite ℕP.+-identityʳ d′ = cong (ℤ._* + suc d′) (ℤP.*-identityʳ (+ t))

ι-∸ : ∀ a b → b ℕ.≤ a → ι (a ℕ.∸ b) ≡ ι a ℚ.- ι b
ι-∸ a b h = ℚP.toℚᵘ-injective
  (ℚᵘP.≃-trans (toℚᵘ-ι (a ℕ.∸ b))
  (ℚᵘP.≃-trans (*≡* (trans (cong (ℤ._* + 1) (pos∸ a b h)) (lem-- (+ a) (+ b))))
  (ℚᵘP.≃-sym (ℚᵘP.≃-trans (ℚP.toℚᵘ-homo-+ (ι a) (ℚ.- ι b))
                           (ℚᵘP.+-cong (toℚᵘ-ι a) (ℚᵘP.≃-trans (ℚP.toℚᵘ-homo‿- (ι b)) (ℚᵘP.-‿cong (toℚᵘ-ι b))))))))

-- `ι t · (1/d) = t/d`
ι-ratio : ∀ t d′ → ι t ℚ.* (+ 1 / suc d′) ≡ + t / suc d′
ι-ratio t d′ = ℚP.toℚᵘ-injective
  (ℚᵘP.≃-trans (ℚP.toℚᵘ-homo-* (ι t) (+ 1 / suc d′))
  (ℚᵘP.≃-trans (ℚᵘP.*-cong (toℚᵘ-ι t) (toℚᵘ-/ (+ 1) d′))
  (ℚᵘP.≃-trans (*≡* (ratio-eq t d′))
  (ℚᵘP.≃-sym (toℚᵘ-/ (+ t) d′)))))
