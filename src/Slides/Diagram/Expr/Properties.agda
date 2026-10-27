{-# OPTIONS --safe --without-K #-}

-- Laws of the symbolic scalars: `evalWith` is an `Ops`-homomorphism, evaluating a weakened term needs one layer, evaluation
-- commutes with substitution, the monad laws of `subst` hold in the free monad's own equality `Eq`, `evalWith` is the
-- generic fold, and it is the unique `Ops`-homomorphism extending an assignment (`evalWith-unique`).
module Slides.Diagram.Expr.Properties where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Container.Core using (position)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; setoid)

open import Container.FreeMonad using (Eq; refl⋆; sym⋆; trans⋆; fmap)

open import Container.FreeMonad.Properties using (bind-cong; bind-pure; bind-assoc)
open import Container.Lowering using (translate)
open import Container.Sum using (inl; inr)

open import Slides.Diagram.Scalar using (Ops; natOps; IsOpsHom)
open import Slides.Diagram.Signature
open import Slides.Diagram.Signature.Properties

open import Slides.Diagram.Expr

evalWith-weakenCore : ∀ {V S} (O : Ops S) (ρ : V → S) (e : Term CoreC V) →
                      evalWith O ρ (weakenCore e) ≡ evalCore (Ops.core O) ρ e
evalWith-weakenCore O ρ e =
  trans (foldT-translate inl (opsH O) ρ e) (foldT-ext _ _ (λ s k → refl) ρ e)

evalWith-weakenSub : ∀ {V S} (O : Ops S) (ρ : V → S) (e : Term SubC V) →
                     evalWith O ρ (weakenSub e) ≡ evalSub (Ops.sub O) ρ e
evalWith-weakenSub O ρ e =
  trans (foldT-translate inr (opsH O) ρ e) (foldT-ext _ _ (λ s k → refl) ρ e)

-- `evalWith` is an `Ops`-homomorphism, by construction: a core and a sub one
evalWith-hom : ∀ {V S} (O : Ops S) (ρ : V → S) → IsOpsHom exprOps O (evalWith O ρ)
evalWith-hom O ρ = record
  { coreHom = record
      { h-0 = refl ; h-+ = λ _ _ → refl ; h-⊔ = λ _ _ → refl
      ; h-fromℕ = λ _ → refl ; h-percentOf = λ _ _ → refl }
  ; subHom = record { h-- = λ _ _ → refl } }

eval-hom : ∀ {V} (ρ : V → ℕ) → IsOpsHom exprOps natOps (eval ρ)
eval-hom = evalWith-hom natOps

-- evaluating a variable is the assignment (the generators)
evalWith-var : ∀ {V S} (O : Ops S) (ρ : V → S) v → evalWith O ρ (var v) ≡ ρ v
evalWith-var O ρ v = refl

subst-hom : ∀ {V W} (σ : V → Expr W) → IsOpsHom exprOps exprOps (subst σ)
subst-hom σ = evalWith-hom exprOps σ

-- one node of the term, built with the constructors, against evaluating it
-- (the constructors present the children as `pick2 a b`; `Eq` below compares trees)
node : ∀ {W S} (O : Ops S) (ρ : W → S) (s : ExprOp) (k : exprArity s → Expr W) →
       evalWith O ρ (opsH (exprOps {W}) .Handler.handle s k) ≡ opsH O .Handler.handle s (λ q → evalWith O ρ (k q))
node O ρ (inj₁ Zero)     k = refl
node O ρ (inj₁ (Lit n))  k = refl
node O ρ (inj₁ Plus)     k = refl
node O ρ (inj₁ Max)      k = refl
node O ρ (inj₁ (Pct p)) k = refl
node O ρ (inj₂ Sub)      k = refl

-- evaluating after substituting is evaluating with the evaluated substitution
evalWith-subst : ∀ {V W S} (O : Ops S) (ρ : W → S) (σ : V → Expr W) (e : Expr V) →
                 evalWith O ρ (subst σ e) ≡ evalWith O (λ v → evalWith O ρ (σ v)) e
evalWith-subst O ρ σ (pure v)         = refl
evalWith-subst O ρ σ (impure (s , k)) =
  trans (node O ρ s (λ q → subst σ (k q)))
        (opsH O .Handler.respects s (λ q → evalWith-subst O ρ σ (k q)))

------------------------------------------------------------------------
-- The free monad's theory
--
-- `Eq` (`Container.FreeMonad`) is equality of trees: same operation at every node,
-- equal leaves.  Two trees that differ only in how a *function* `arity → Expr V` is
-- presented (`pick2 a b` against `k`) are `Eq` but not `≡` without extensionality, so
-- the monad laws are stated in `Eq` over the `≡`-setoid of the variables.

private
  E : (W : Set) → Expr W → Expr W → Set
  E W = Eq {C = ExprC} (setoid W)

-- a node `impure (s , k)` is `Eq` to the same node built by the constructors
node-eq : ∀ {V} (s : ExprOp) (k : exprArity s → Expr V) →
          E V (impure (s , k)) (opsH (exprOps {V}) .Handler.handle s k)
node-eq (inj₁ Zero)     k = refl , λ ()
node-eq (inj₁ (Lit n))  k = refl , λ ()
node-eq {V} (inj₁ Plus) k = refl , two k
  where two : ∀ (k : Fin 2 → Expr V) → ∀ q → E V (k q) (pick2 (k zero) (k (suc zero)) q)
        two k zero = refl⋆ (setoid V) _
        two k (suc zero) = refl⋆ (setoid V) _
        two k (suc (suc ()))
node-eq {V} (inj₁ Max) k = refl , two k
  where two : ∀ (k : Fin 2 → Expr V) → ∀ q → E V (k q) (pick2 (k zero) (k (suc zero)) q)
        two k zero = refl⋆ (setoid V) _
        two k (suc zero) = refl⋆ (setoid V) _
        two k (suc (suc ()))
node-eq {V} (inj₁ (Pct p)) k = refl , λ _ → refl⋆ (setoid V) _
node-eq {V} (inj₂ Sub) k = refl , two k
  where two : ∀ (k : Fin 2 → Expr V) → ∀ q → E V (k q) (pick2 (k zero) (k (suc zero)) q)
        two k zero = refl⋆ (setoid V) _
        two k (suc zero) = refl⋆ (setoid V) _
        two k (suc (suc ()))

-- `subst` is the free monad's bind
subst-bind : ∀ {V W} (σ : V → Expr W) (e : Expr V) → E W (subst σ e) (e >>= σ)
subst-bind σ (pure v)         = refl⋆ (setoid _) _
subst-bind σ (impure (s , k)) =
  trans⋆ (setoid _) (sym⋆ (setoid _) (node-eq s (λ q → subst σ (k q))))
         (refl , λ q → subst-bind σ (k q))

-- `rename` is the functor action
rename-fmap : ∀ {V W} (f : V → W) (e : Expr V) → E W (rename f e) (fmap f e)
rename-fmap f = subst-bind (λ v → var (f v))

-- monad laws for `subst`
subst-var : ∀ {V W} (σ : V → Expr W) (v : V) → subst σ (var v) ≡ σ v
subst-var σ v = refl

subst-pure : ∀ {V} (e : Expr V) → E V (subst var e) e
subst-pure e = trans⋆ (setoid _) (subst-bind var e) (bind-pure (setoid _) e)

subst-assoc : ∀ {U V W} (σ : U → Expr V) (τ : V → Expr W) (e : Expr U) →
              E W (subst τ (subst σ e)) (subst (λ u → subst τ (σ u)) e)
subst-assoc {W = W} σ τ e =
  trans⋆ (setoid W) (subst-bind τ (subst σ e))
 (trans⋆ (setoid W) (bind-cong {A = setoid _} {B = setoid W} (subst-bind σ e) (λ { refl → refl⋆ (setoid W) _ }))
 (trans⋆ (setoid W) (bind-assoc (setoid _) (setoid _) (setoid W) e σ τ)
 (trans⋆ (setoid W)
    (bind-cong {A = setoid _} {B = setoid W} (refl⋆ (setoid _) e)
       (λ { {x} refl → sym⋆ (setoid W) (subst-bind τ (σ x)) }))
    (sym⋆ (setoid W) (subst-bind (λ u → subst τ (σ u)) e)))))

------------------------------------------------------------------------
-- `evalWith` is the generic fold (`Container.FreeMonad.Algebraic`)

-- the concrete fold is the generic one (`Signature.Generic.fold-agrees`)
module GE = Generic {ExprC}

evalWith-generic : ∀ {V S} (O : Ops S) (ρ : V → S) (e : Expr V) →
                   GE.G.fold (GE.algebra (opsH O)) (GE.assign ρ) e ≡ evalWith O ρ e
evalWith-generic O ρ = GE.fold-agrees (opsH O) ρ

------------------------------------------------------------------------
-- Initiality: the free algebra's universal property
--
-- Any `Ops`-homomorphism out of `Expr V` is `evalWith` of its values on the variables.
-- (The homomorphism is assumed to respect `Eq` -- it cannot fail to, but showing
-- it needs function extensionality, since `a ⊞ b` presents its children as `pick2 a b`.)

-- a homomorphism commutes with every node
hom-node : ∀ {V S} (O : Ops S) (h : Expr V → S) → IsOpsHom exprOps O h →
           ∀ s (k : exprArity s → Expr V) →
           h (opsH (exprOps {V}) .Handler.handle s k) ≡ opsH O .Handler.handle s (λ q → h (k q))
hom-node O h hom (inj₁ Zero)     k = IsOpsHom.h-0 hom
hom-node O h hom (inj₁ (Lit n))  k = IsOpsHom.h-fromℕ hom n
hom-node O h hom (inj₁ Plus)     k = IsOpsHom.h-+ hom (k zero) (k (suc zero))
hom-node O h hom (inj₁ Max)      k = IsOpsHom.h-⊔ hom (k zero) (k (suc zero))
hom-node O h hom (inj₁ (Pct p))  k = IsOpsHom.h-percentOf hom p (k tt)
hom-node O h hom (inj₂ Sub)      k = IsOpsHom.h-- hom (k zero) (k (suc zero))

evalWith-unique : ∀ {V S} (O : Ops S) (h : Expr V → S) → IsOpsHom exprOps O h →
                  (∀ {t u} → E V t u → h t ≡ h u) →
                  ∀ e → h e ≡ evalWith O (λ v → h (var v)) e
evalWith-unique O h hom ext (pure v)         = refl
evalWith-unique O h hom ext (impure (s , k)) =
  trans (ext (node-eq s k))
 (trans (hom-node O h hom s k)
        (opsH O .Handler.respects s (λ q → evalWith-unique O h hom ext (k q))))
