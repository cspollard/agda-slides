{-# OPTIONS --safe --without-K #-}

-- Symbolic scalars: the free `Ops`-algebra.
--
-- A layout is computed in a scalar `Ops S` (`Slides.Diagram.Scalar`).  Take the scalar
-- to be an *expression*: the terms built from literals and the operations the layout
-- uses (sum, difference, maximum, "p percent of"), over a set `V` of variables.  Those
-- terms are the free monad on a container,
--
--     Expr V = ExprC ⋆ V          ExprC = ExprOp ▷ exprArity
--
-- whose leaves are variables, so that
--
--   * `Expr V` is an `Ops` (`exprOps`: the operations are the constructors, with
--     `0#` the zero): laying a diagram out *in* `Expr V` leaves every coordinate
--     as a formula, computed once;
--   * `>>=` is substitution (`rename`, `subst`), `pure` a variable;
--   * `evalWith O ρ : Expr V → S` is the fold, the unique `Ops`-map extending an
--     assignment `ρ : V → S` (the free algebra's universal property), and it is an
--     `Ops`-homomorphism by construction (`evalWith-hom`, equalities of the form
--     `refl`).  `eval ρ` is the instance at ℕ.
--
-- A template body of an animation (`Slides.Anim.Syntax`) has one variable, the segment's
-- parameter (`t : Expr ⊤`); a whole animation has one variable per segment, so that
-- segments played together keep independent parameters.
--
-- `toℕ` has no meaning for a formula; `exprOps` takes the value at the all-zero
-- assignment.  It is not part of `IsOpsHom` and layout never applies it.

module Slides.Diagram.Expr where

open import Level using (0ℓ)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Data.Container.Core using (Container; _▷_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Slides.Diagram.Scalar using (Ops; natOps; IsOpsHom)

------------------------------------------------------------------------
-- The signature

data ExprOp : Set where
  Zero           : ExprOp           -- `0#`
  Lit            : ℕ → ExprOp       -- the scalar `fromℕ n`
  Plus Monus Max : ExprOp
  Pct            : ℕ → ExprOp       -- `percentOf p`

exprArity : ExprOp → Set
exprArity Zero     = ⊥
exprArity (Lit _)  = ⊥
exprArity Plus     = Fin 2
exprArity Monus    = Fin 2
exprArity Max      = Fin 2
exprArity (Pct _)  = ⊤

ExprC : Container 0ℓ 0ℓ
ExprC = ExprOp ▷ exprArity

Expr : Set → Set
Expr V = ExprC ⋆ V

private
  pick2 : ∀ {A : Set} → A → A → Fin 2 → A
  pick2 a b zero          = a
  pick2 a b (suc zero)    = b
  pick2 a b (suc (suc ()))

var : ∀ {V} → V → Expr V
var = pure

-- the parameter of a template
t : Expr ⊤
t = pure tt

zero′ : ∀ {V} → Expr V
zero′ = impure (Zero , λ ())

lit : ∀ {V} → ℕ → Expr V
lit n = impure (Lit n , λ ())

infixl 6 _⊞_ _⊖_
infixl 7 _⊓_
_⊞_ _⊖_ _⊓_ : ∀ {V} → Expr V → Expr V → Expr V
a ⊞ b = impure (Plus , pick2 a b)
a ⊖ b = impure (Monus , pick2 a b)
a ⊓ b = impure (Max , pick2 a b)

pct : ∀ {V} → ℕ → Expr V → Expr V
pct p a = impure (Pct p , λ _ → a)

------------------------------------------------------------------------
-- Evaluation: the fold, into any scalar

evalWith : ∀ {V S} → Ops S → (V → S) → Expr V → S
evalWith O ρ (pure v)                  = ρ v
evalWith O ρ (impure (Zero , _))     = Ops.0# O
evalWith O ρ (impure (Lit n , _))      = Ops.fromℕ O n
evalWith O ρ (impure (Plus , k))       = Ops._+_ O (evalWith O ρ (k zero)) (evalWith O ρ (k (suc zero)))
evalWith O ρ (impure (Monus , k))      = Ops._-_ O (evalWith O ρ (k zero)) (evalWith O ρ (k (suc zero)))
evalWith O ρ (impure (Max , k))        = Ops._⊔_ O (evalWith O ρ (k zero)) (evalWith O ρ (k (suc zero)))
evalWith O ρ (impure (Pct p , k))      = Ops.percentOf O p (evalWith O ρ (k tt))

-- at the naturals
eval : ∀ {V} → (V → ℕ) → Expr V → ℕ
eval = evalWith natOps

-- substitution
subst : ∀ {V W} → (V → Expr W) → Expr V → Expr W
subst σ e = e >>= σ

rename : ∀ {V W} → (V → W) → Expr V → Expr W
rename f = subst (λ v → pure (f v))

------------------------------------------------------------------------
-- The `Ops` structure

exprOps : ∀ {V} → Ops (Expr V)
exprOps = record
  { 0# = zero′ ; _+_ = _⊞_ ; _-_ = _⊖_ ; _⊔_ = _⊓_ ; fromℕ = lit
  ; toℕ = eval (λ _ → 0) ; percentOf = pct }

-- `evalWith` is an `Ops`-homomorphism, by construction
evalWith-hom : ∀ {V S} (O : Ops S) (ρ : V → S) → IsOpsHom exprOps O (evalWith O ρ)
evalWith-hom O ρ = record
  { h-0 = refl ; h-+ = λ _ _ → refl ; h-- = λ _ _ → refl ; h-⊔ = λ _ _ → refl
  ; h-fromℕ = λ _ → refl ; h-percentOf = λ _ _ → refl }

eval-hom : ∀ {V} (ρ : V → ℕ) → IsOpsHom exprOps natOps (eval ρ)
eval-hom = evalWith-hom natOps

-- evaluating a variable is the assignment (the generators)
evalWith-var : ∀ {V S} (O : Ops S) (ρ : V → S) v → evalWith O ρ (var v) ≡ ρ v
evalWith-var O ρ v = refl
