{-# OPTIONS --safe --without-K #-}

-- Laws of signatures and handlers: a handler is an algebra of the polynomial functor (`toAlgebra`) and `⊕` is the
-- copairing, `foldT` is the generic fold of `Container.FreeMonad.Algebraic` (`Generic.fold-agrees`), folding a weakened
-- term is folding with the restricted handler (`foldT-translate`), and weakening is a monad morphism (`weaken-bind`).
module Slides.Diagram.Signature.Properties where

open import Level using (0ℓ)
open import Data.Container.Core using (Container; _⇒_; shape; position)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Container.Relation.Binary.Pointwise using () renaming (_,_ to _,ₚ_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; setoid)

open import Container.FreeMonad.Algebraic using (module Alg)
open import Container.Lowering using (translate; embed)
open import Container.Lowering.Properties using (lower-embed; lower-bind; _≈⋆_; sym≈; trans≈; bind-cong≈)
open import Container.Polynomial using (Poly₀)
import Container.Sum as Sum

open import Slides.Diagram.Signature
open Handler

foldT-⊕₁ : ∀ {Σ₁ Σ₂ V S} (H₁ : Handler Σ₁ S) (H₂ : Handler Σ₂ S) (ρ : V → S) s k →
           foldT (H₁ ⊕ H₂) ρ (impure (inj₁ s , k)) ≡ H₁ .handle s (λ q → foldT (H₁ ⊕ H₂) ρ (k q))
foldT-⊕₁ H₁ H₂ ρ s k = refl

------------------------------------------------------------------------
-- A handler is an algebra of the container, and `⊕` is the copairing

module _ {Σ : Sig} {S : Set} where

  toAlgebra : Handler Σ S → Func (Poly₀ Σ (setoid S)) (setoid S)
  toAlgebra H = record
    { to   = λ { (s , k) → H .handle s k }
    ; cong = λ { {s , _} {.s , _} (refl ,ₚ e) → H .respects s e } }

module _ {Σ₁ Σ₂ : Sig} {S : Set} (H₁ : Handler Σ₁ S) (H₂ : Handler Σ₂ S) where

  toAlgebra-⊕ : ∀ x → toAlgebra (H₁ ⊕ H₂) ⟨$⟩ x
                      ≡ Sum.copair Σ₁ Σ₂ (setoid S) (toAlgebra H₁) (toAlgebra H₂) ⟨$⟩ x
  toAlgebra-⊕ (inj₁ s , k) = refl
  toAlgebra-⊕ (inj₂ s , k) = refl

------------------------------------------------------------------------
-- The fold is the generic one

module Generic {Σ : Sig} where
  module G = Alg 0ℓ 0ℓ Σ
  open import Categories.Functor.Algebra using (F-Algebra)

  algebra : ∀ {S} → Handler Σ S → F-Algebra G.F
  algebra {S} H = record { A = setoid S ; α = toAlgebra H }

  assign : ∀ {V S : Set} → (V → S) → Func (setoid V) (setoid S)
  assign ρ = record { to = ρ ; cong = cong ρ }
    where open import Relation.Binary.PropositionalEquality using (cong)

  fold-agrees : ∀ {V S} (H : Handler Σ S) (ρ : V → S) (e : Term Σ V) →
                G.fold (algebra H) (assign ρ) e ≡ foldT H ρ e
  fold-agrees H ρ (pure v)         = refl
  fold-agrees H ρ (impure (s , k)) = H .respects s (λ i → fold-agrees H ρ (k i))

-- folding a weakened term is folding it with the restricted handler
foldT-translate : ∀ {Σ Σ′ V S} (m : Σ ⇒ Σ′) (H : Handler Σ′ S) (ρ : V → S) (e : Term Σ V) →
                  foldT H ρ (translate m e) ≡ foldT (restrict m H) ρ e
foldT-translate m H ρ (pure v)         = refl
foldT-translate m H ρ (impure (s , k)) =
  H .respects (shape m s) (λ q → foldT-translate m H ρ (k (position m q)))

-- handlers that agree command by command give the same fold
foldT-ext : ∀ {Σ V S} (H H′ : Handler Σ S) → (∀ s k → H .handle s k ≡ H′ .handle s k) →
            (ρ : V → S) (e : Term Σ V) → foldT H ρ e ≡ foldT H′ ρ e
foldT-ext H H′ eq ρ (pure v)         = refl
foldT-ext H H′ eq ρ (impure (s , k)) =
  trans (eq s _) (H′ .respects s (λ q → foldT-ext H H′ eq ρ (k q)))

-- Weakening is a monad morphism (up to equality of programs, as in
-- `Container.Lowering`): it commutes with substitution.
weaken-bind : ∀ {Σ Σ′ V W} (m : Σ ⇒ Σ′) (e : Term Σ V) (σ : V → Term Σ W) →
              translate m (e >>= σ) ≈⋆ (translate m e >>= λ v → translate m (σ v))
weaken-bind m e σ =
  trans≈ (sym≈ (lower-embed m (e >>= σ)))
 (trans≈ (lower-bind (embed m) e σ)
         (bind-cong≈ (lower-embed m e) (λ v → lower-embed m (σ v))))
