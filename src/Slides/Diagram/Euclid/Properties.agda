{-# OPTIONS --safe --without-K #-}

-- Laws of the discrete templates: `evalD` is a homomorphism of all three layers, evaluation commutes with substitution,
-- weakening is a homomorphism and evaluates to the original.
module Slides.Diagram.Euclid.Properties where

open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Container.Core using (Shape; Position)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Slides.Diagram.Scalar
open import Slides.Diagram.Signature
open import Slides.Diagram.Expr
open import Slides.Diagram.Expr.Properties

open import Slides.Diagram.Euclid

-- `evalD` is a homomorphism of all three layers, by construction
evalD-hom : ∀ {V S} (D : DiscreteOps S) (ρ : V → S) →
            IsOpsHom dexprOps (DiscreteOps.ops D) (evalD D ρ)
evalD-hom D ρ = record
  { coreHom = record
      { h-0 = refl ; h-+ = λ _ _ → refl ; h-⊔ = λ _ _ → refl
      ; h-fromℕ = λ _ → refl ; h-percentOf = λ _ _ → refl }
  ; subHom = record { h-- = λ _ _ → refl } }

evalD-euclid-hom : ∀ {V S} (D : DiscreteOps S) (ρ : V → S) →
                   IsEuclidHom termEuclid (DiscreteOps.euclid D) (evalD D ρ)
evalD-euclid-hom D ρ = record
  { h-divBy = λ _ _ → refl ; h-modBy = λ _ _ → refl ; h-mulLit = λ _ _ → refl ; h-lt = λ _ _ _ _ → refl }

evalD-hom-ℕ : ∀ {V} (ρ : V → ℕ) → IsOpsHom dexprOps natOps (evalD natD ρ)
evalD-hom-ℕ = evalD-hom natD

substD-hom : ∀ {V W} (σ : V → DExpr W) → IsOpsHom dexprOps dexprOps (substD σ)
substD-hom σ = evalD-hom dexprD σ

nodeD : ∀ {W S} (D : DiscreteOps S) (ρ : W → S) (s : Shape DExprC) (k : Position DExprC s → DExpr W) →
        evalD D ρ (dH (dexprD {W}) .Handler.handle s k) ≡ dH D .Handler.handle s (λ q → evalD D ρ (k q))
nodeD D ρ (inj₁ (inj₁ Zero))     k = refl
nodeD D ρ (inj₁ (inj₁ (Lit n)))  k = refl
nodeD D ρ (inj₁ (inj₁ Plus))     k = refl
nodeD D ρ (inj₁ (inj₁ Max))      k = refl
nodeD D ρ (inj₁ (inj₁ (Pct p)))  k = refl
nodeD D ρ (inj₁ (inj₂ Sub))      k = refl
nodeD D ρ (inj₂ (DivBy d))       k = refl
nodeD D ρ (inj₂ (ModBy d))       k = refl
nodeD D ρ (inj₂ (MulLit n))      k = refl
nodeD D ρ (inj₂ Lt)              k = refl

-- evaluating after substituting is evaluating with the evaluated substitution
evalD-substD : ∀ {V W S} (D : DiscreteOps S) (ρ : W → S) (σ : V → DExpr W) (e : DExpr V) →
               evalD D ρ (substD σ e) ≡ evalD D (λ v → evalD D ρ (σ v)) e
evalD-substD D ρ σ (pure v)         = refl
evalD-substD D ρ σ (impure (s , k)) =
  trans (nodeD D ρ s (λ q → substD σ (k q)))
        (dH D .Handler.respects s (λ q → evalD-substD D ρ σ (k q)))

weakenE-hom : ∀ {V} → IsOpsHom (exprOps {V}) dexprOps weakenE
weakenE-hom = evalWith-hom dexprOps pure

-- read with the operations of the first two layers only
evalD-weaken : ∀ {V S} (D : DiscreteOps S) (ρ : V → S) (e : Expr V) →
               evalD D ρ (weakenE e) ≡ evalWith (DiscreteOps.ops D) ρ e
evalD-weaken D ρ (pure v)         = refl
evalD-weaken D ρ (impure (s , k)) =
  trans (nodeD D ρ (inj₁ s) (λ q → weakenE (k q)))
        (opsH (DiscreteOps.ops D) .Handler.respects s (λ q → evalD-weaken D ρ (k q)))
