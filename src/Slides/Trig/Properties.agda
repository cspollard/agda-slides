{-# OPTIONS --safe --without-K #-}

-- What `Slides.Trig` can promise without real numbers: at the origin the polynomials are exact
-- (cos 0 = 1 and sin 0 = 0 at every order).  Accuracy away from 0 is a statement about ℝ; it is
-- checked on closed values in `Slides.Trig.Check`.

module Slides.Trig.Properties where

open import Data.Integer using (+_)
open import Data.Nat using (ℕ; zero; suc; _/_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (ℚᵘ; mkℚᵘ; 0ℚᵘ; 1ℚᵘ; _≃_; *≡*; _*_; _-_)
open import Data.Rational.Unnormalised.Properties
open import Relation.Binary.PropositionalEquality using (refl)

open import Slides.Trig

-- a vanishing factor kills a product
kill : ∀ {a} b → a ≃ 0ℚᵘ → a * b ≃ 0ℚᵘ
kill b a₀ = ≃-trans (*-congʳ a₀) (*-zeroˡ b)

-- with t = 0 the correction of the series vanishes: the tail is 1
tail-zero : ∀ k m t → t ≃ 0ℚᵘ → tail k m t ≃ 1ℚᵘ
tail-zero zero    m t _  = ≃-refl
tail-zero (suc k) m t t₀ = ≃-trans (+-congʳ 1ℚᵘ (-‿cong (kill _ (kill _ t₀)))) (+-identityʳ 1ℚᵘ)

-- the eighth-turn polynomials at 0
eighth-zero : ∀ n x → x ≃ 0ℚᵘ → (proj₁ (eighth n x) ≃ 1ℚᵘ) × (proj₂ (eighth n x) ≃ 0ℚᵘ)
eighth-zero n x x₀ = tail-zero (n / 2) 1 _ (kill _ θ₀) , kill _ θ₀
  where θ₀ : tau * x ≃ 0ℚᵘ
        θ₀ = ≃-trans (*-congˡ {tau} x₀) (*-zeroʳ tau)

cis-zero : ∀ n → (cos n 0ℚᵘ ≃ 1ℚᵘ) × (sin n 0ℚᵘ ≃ 0ℚᵘ)
cis-zero n = eighth-zero n (0ℚᵘ - mkℚᵘ (+ 0) 3) (*≡* refl)
