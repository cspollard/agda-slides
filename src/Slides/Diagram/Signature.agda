{-# OPTIONS --safe --without-K #-}

-- Signatures of scalar operations, as containers, and their algebras.
--
-- The scalar operations of a layout come in layers (`Slides.Diagram.Scalar`: `CoreOps`,
-- `SubOps`; `Slides.Diagram.Expr` and `Slides.Diagram.Ordered` give each layer its
-- signature).  A signature is a container `Σ = Op ▷ arity`; the symbolic scalars over
-- it are the free monad `Term Σ V = Σ ⋆ V` (leaves are variables).  Signatures are
-- combined by the sum of containers (`Data.Container.Combinator._⊎_`), and a term over a
-- layer is a term over any larger signature along the inclusion (`weaken`, the
-- translation along a container morphism, `Container.Lowering.translate`).
--
-- What interprets a signature in a carrier `S` is an algebra of the container; here a
-- `Handler Σ S`: one function per command, taking the values of its arguments, and
-- respecting pointwise-equal arguments (this holds for every handler the layers
-- define, without function extensionality, because their arities are finite).  This is
-- exactly an algebra of the polynomial functor on the `≡`-setoid of `S`
-- (`toAlgebra`), and
--
--   * a handler for a sum is a pair of handlers (`_⊕_`; it is `Container.Sum.copair` of
--     the algebras, `toAlgebra-⊕`), so evaluation is modular: each layer is interpreted by
--     its own record of operations and the interpretation of a sum is the copairing;
--   * `foldT H ρ : Term Σ V → S` is the fold, the unique extension of the assignment
--     `ρ : V → S` to an algebra map; it is the generic fold of
--     `Container.FreeMonad.Algebraic` (`fold-agrees`);
--   * along an inclusion, folding a weakened term is folding the original with the
--     handler restricted (`foldT-translate`), which is what makes the layers independent.

module Slides.Diagram.Signature where

open import Level using (0ℓ)
open import Data.Container.Core using (Container; Shape; Position; _⇒_; shape; position)
open import Data.Container.Combinator using (_⊎_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

Sig : Set₁
Sig = Container 0ℓ 0ℓ

-- symbolic scalars over a signature
Term : Sig → Set → Set
Term Σ V = Σ ⋆ V

record Handler (Σ : Sig) (S : Set) : Set where
  field
    handle : (s : Shape Σ) → (Position Σ s → S) → S
    respects : ∀ s {k k′ : Position Σ s → S} → (∀ i → k i ≡ k′ i) → handle s k ≡ handle s k′

open Handler

-- the algebra of a sum is a pair of algebras
infixr 5 _⊕_
_⊕_ : ∀ {Σ₁ Σ₂ S} → Handler Σ₁ S → Handler Σ₂ S → Handler (Σ₁ ⊎ Σ₂) S
(H₁ ⊕ H₂) .handle (inj₁ s) k = H₁ .handle s k
(H₁ ⊕ H₂) .handle (inj₂ s) k = H₂ .handle s k
(H₁ ⊕ H₂) .respects (inj₁ s) e = H₁ .respects s e
(H₁ ⊕ H₂) .respects (inj₂ s) e = H₂ .respects s e

-- the fold
foldT : ∀ {Σ V S} → Handler Σ S → (V → S) → Term Σ V → S
foldT H ρ (pure v)          = ρ v
foldT H ρ (impure (s , k))  = H .handle s (λ q → foldT H ρ (k q))

------------------------------------------------------------------------
-- Inclusions

-- restriction of a handler along a container morphism
restrict : ∀ {Σ Σ′ S} → Σ ⇒ Σ′ → Handler Σ′ S → Handler Σ S
restrict m H .handle s k = H .handle (shape m s) (λ q → k (position m q))
restrict m H .respects s e   = H .respects (shape m s) (λ q → e (position m q))
