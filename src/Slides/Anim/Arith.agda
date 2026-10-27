{-# OPTIONS --safe --without-K #-}

-- THEORY MODULE: proofs and the vocabulary they need; no executable imports it (`tests/check_closure.py`).
--
-- The boolean comparisons of ticks (`_<ᵇ_`, `_≤ᵇ_`, what the frame functions branch on) against
-- the propositional order the proofs use.  Shared by the assembly proofs
-- (`Slides.Anim.Assembly` and its `Leaf` and `Continuous` parts) and the phases (`Slides.Anim.Phases.Properties`).

module Slides.Anim.Arith where

open import Data.Bool using (Bool; true; false; T)
open import Data.Nat as ℕ using (ℕ; zero; suc; _<ᵇ_; _≤ᵇ_; _≤_; _<_)
import Data.Nat.Properties as ℕP
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Data.Unit using (tt)

T⇒≡ : ∀ {b} → T b → b ≡ true
T⇒≡ {true} _ = refl

<ᵇ-true : ∀ {m n} → m < n → (m <ᵇ n) ≡ true
<ᵇ-true h = T⇒≡ (ℕP.<⇒<ᵇ h)

≤ᵇ-true : ∀ {m n} → m ≤ n → (m ≤ᵇ n) ≡ true
≤ᵇ-true h = T⇒≡ (ℕP.≤⇒≤ᵇ h)

<ᵇ-lt : ∀ {m n} → (m <ᵇ n) ≡ true → m < n
<ᵇ-lt {m} {n} h = ℕP.<ᵇ⇒< m n (subst T (sym h) tt)

<ᵇ-ge : ∀ {m n} → (m <ᵇ n) ≡ false → n ≤ m
<ᵇ-ge {m} {n} h = ℕP.≮⇒≥ (λ lt → subst T h (ℕP.<⇒<ᵇ lt))

<ᵇ-false : ∀ {m n} → n ≤ m → (m <ᵇ n) ≡ false
<ᵇ-false {m} {zero}  ℕ.z≤n         = refl
<ᵇ-false {suc m} {suc n} (ℕ.s≤s h) = <ᵇ-false h
