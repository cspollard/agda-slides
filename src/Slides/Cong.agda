{-# OPTIONS --safe --without-K #-}

-- `cong` at three and four arguments (the standard library stops at `cong₂`).

module Slides.Cong where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a′ b b′ c c′} →
        a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
cong₃ f refl refl refl = refl

cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E) {a a′ b b′ c c′ d d′} →
        a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ → f a b c d ≡ f a′ b′ c′ d′
cong₄ f refl refl refl refl = refl
