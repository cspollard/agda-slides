{-# OPTIONS --safe --without-K #-}

-- Signatures of scalar operations, as containers, and their algebras.
--
-- The scalar operations of a layout come in layers (`Slides.Diagram.Scalar`: `CoreOps`,
-- `SubOps`; `Slides.Diagram.Expr` and `Slides.Diagram.Euclid` give each layer its
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
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Container.Relation.Binary.Pointwise using () renaming (_,_ to _,ₚ_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; setoid)

open import Container.FreeMonad.Algebraic using (module Alg)
open import Container.Lowering using (translate; embed; lower-embed; lower-bind; _≈⋆_; sym≈; trans≈; bind-cong≈)
open import Container.Polynomial using (Poly₀)
import Container.Sum as Sum

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

------------------------------------------------------------------------
-- Inclusions

-- restriction of a handler along a container morphism
restrict : ∀ {Σ Σ′ S} → Σ ⇒ Σ′ → Handler Σ′ S → Handler Σ S
restrict m H .handle s k = H .handle (shape m s) (λ q → k (position m q))
restrict m H .respects s e   = H .respects (shape m s) (λ q → e (position m q))

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
