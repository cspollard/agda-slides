{-# OPTIONS --safe --without-K #-}

-- A signature split into a *tag* and a *payload*: `Tagged arity P` has the commands `(t , p)` with
-- `p : P t`, and the positions of a command are those of its tag (`arity t`), whatever the payload.
--
-- A map of payloads `φ : P t → Q t` is then a container morphism with the identity on positions
-- (`over φ`), and translating along it is functorial in `φ` (`over-id`, `over-∘`) with no case
-- analysis on the tag.  A change of scalar in a language whose payloads hold scalars is such a map.

module Container.Tagged where

open import Level using (0ℓ; lift)
open import Function.Base using (id; _∘_)
open import Data.Product.Base using (Σ; _,_; proj₁)
open import Data.Container.Core using (Container; _▷_; _⇒_; Position)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)

open import Container.Lowering using (_≈⋆_; translate)

module _ {Tag : Set} (arity : Tag → Set) where

  Tagged : (Tag → Set) → Container 0ℓ 0ℓ
  Tagged P = Σ Tag P ▷ (arity ∘ proj₁)

  over : ∀ {P Q : Tag → Set} → (∀ t → P t → Q t) → Tagged P ⇒ Tagged Q
  over φ = record { shape = λ { (t , p) → t , φ t p } ; position = id }

  -- positions are not touched by an equality of payloads
  module _ {P : Tag → Set} {X : Set} where
    private
      subst-pos : ∀ {t} {p p′ : P t} (e : p ≡ p′) (q : arity t) →
                  subst (Position (Tagged P)) (cong (t ,_) e) q ≡ q
      subst-pos refl q = refl

    step : ∀ {t} {p p′ : P t} (e : p ≡ p′) (k : arity t → Tagged P ⋆ X) {a : Tagged P ⋆ X} q →
           a ≈⋆ k q → a ≈⋆ k (subst (Position (Tagged P)) (cong (t ,_) e) q)
    step e k q = subst (λ q′ → _ ≈⋆ k q′) (sym (subst-pos e q))

  module _ {P : Tag → Set} {X : Set} where

    over-id : ∀ (φ : ∀ t → P t → P t) → (∀ t p → φ t p ≡ p) → ∀ (d : Tagged P ⋆ X) → translate (over φ) d ≈⋆ d
    over-id φ e (pure _)               = lift refl
    over-id φ e (impure ((t , p) , k)) = cong (t ,_) (e t p) , λ q → step (e t p) k q (over-id φ e (k q))

  module _ {P Q R : Tag → Set} {X : Set} where

    over-∘ : ∀ (ψ : ∀ t → Q t → R t) (φ : ∀ t → P t → Q t) (χ : ∀ t → P t → R t) → (∀ t p → ψ t (φ t p) ≡ χ t p) →
             ∀ (d : Tagged P ⋆ X) → translate (over ψ) (translate (over φ) d) ≈⋆ translate (over χ) d
    over-∘ ψ φ χ e (pure _)               = lift refl
    over-∘ ψ φ χ e (impure ((t , p) , k)) =
      cong (t ,_) (e t p) , λ q → step (e t p) (λ q′ → translate (over χ) (k q′)) q (over-∘ ψ φ χ e (k q))
