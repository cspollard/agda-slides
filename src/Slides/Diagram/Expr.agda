{-# OPTIONS --safe --without-K #-}

-- The first two layers of the scalar signature: core and sub.
--
-- A layout is computed in a scalar `Ops S` (`Slides.Diagram.Scalar`).  The symbolic scalars are
-- terms of a signature (`Slides.Diagram.Signature`: `Term Σ V = Σ ⋆ V`, the free monad on a
-- container), and the signature is made of *layers*, composed as a sum of containers
-- (`Data.Container.Combinator._⊎_`):
--
--     CoreC = CoreOp ▷ coreArity     zero, literal `fromℕ n`, plus, max, `pct p`
--     SubC  = SubOp  ▷ subArity      sub  (monus in ℕ, real subtraction in ℤ, ℚ)
--     ExprC = CoreC ⊎ SubC           the layers every scalar has
--
-- Each layer is interpreted by its own record of operations (`CoreOps`, `SubOps`), and the
-- interpretation of a sum is the copairing of the two (`Signature._⊕_`, which is
-- `Container.Sum.copair`).  The smart constructors (`zero′`, `lit`, `_⊞_`, `_⊓_`, `pct`; `_⊖_`) are
-- written once for any signature with a container morphism from the layer (`CoreSyntax`,
-- `SubSyntax`).  The language of symbolic scalars that the rest of the library uses has two more
-- layers, ordered and floor, and is `Slides.Diagram.Ordered.OExpr`; this module is its base.

module Slides.Diagram.Expr where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Data.Container.Core using (Shape; Position; _▷_; _⇒_; shape; position)
open import Data.Container.Combinator using (_⊎_)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.PropositionalEquality using (refl; cong; cong₂)

open import Container.Lowering using (translate)
open import Container.Pick using (pick2)
open import Container.Sum using (inl; inr)

open import Slides.Diagram.Scalar using (Ops; CoreOps; SubOps; natOps)
open import Slides.Diagram.Signature

------------------------------------------------------------------------
-- The layers

-- core: `0#`, the scalar `fromℕ n`, `+`, `⊔`, `percentOf p`
data CoreOp : Set where
  Zero      : CoreOp
  Lit       : ℕ → CoreOp
  Plus Max  : CoreOp
  Pct       : ℕ → CoreOp

coreArity : CoreOp → Set
coreArity Zero     = ⊥
coreArity (Lit _)  = ⊥
coreArity Plus     = Fin 2
coreArity Max      = Fin 2
coreArity (Pct _)  = ⊤

CoreC : Sig
CoreC = CoreOp ▷ coreArity

-- difference, in its own layer: one symbol, laws that depend on the scalar
data SubOp : Set where
  Sub : SubOp

subArity : SubOp → Set
subArity Sub = Fin 2

SubC : Sig
SubC = SubOp ▷ subArity

-- the signature of the layout's scalar
ExprC : Sig
ExprC = CoreC ⊎ SubC

ExprOp : Set
ExprOp = Shape ExprC            -- CoreOp ⊎ SubOp

exprArity : ExprOp → Set
exprArity = Position ExprC

------------------------------------------------------------------------
-- Constructors, for any signature containing a layer

module CoreSyntax {Σ : Sig} (i : CoreC ⇒ Σ) where
  zero′ : ∀ {V} → Term Σ V
  zero′ = impure (shape i Zero , λ q → ⊥-elim (position i q))

  lit : ∀ {V} → ℕ → Term Σ V
  lit n = impure (shape i (Lit n) , λ q → ⊥-elim (position i q))

  infixl 6 _⊞_
  infixl 7 _⊓_
  _⊞_ _⊓_ : ∀ {V} → Term Σ V → Term Σ V → Term Σ V
  a ⊞ b = impure (shape i Plus , λ q → pick2 a b (position i q))
  a ⊓ b = impure (shape i Max , λ q → pick2 a b (position i q))

  pct : ∀ {V} → ℕ → Term Σ V → Term Σ V
  pct p a = impure (shape i (Pct p) , λ _ → a)

  -- the terms of the layer's signature are a `CoreOps`
  termCore : ∀ {V} → CoreOps (Term Σ V)
  termCore = record { 0# = zero′ ; _+_ = _⊞_ ; _⊔_ = _⊓_ ; fromℕ = lit ; percentOf = pct }

module SubSyntax {Σ : Sig} (j : SubC ⇒ Σ) where
  infixl 6 _⊖_
  _⊖_ : ∀ {V} → Term Σ V → Term Σ V → Term Σ V
  a ⊖ b = impure (shape j Sub , λ q → pick2 a b (position j q))

  termSub : ∀ {V} → SubOps (Term Σ V)
  termSub = record { _-_ = _⊖_ }

------------------------------------------------------------------------
-- Interpretation: one handler per layer, copaired

coreH : ∀ {S} → CoreOps S → Handler CoreC S
coreH O .Handler.handle Zero     k = CoreOps.0# O
coreH O .Handler.handle (Lit n)  k = CoreOps.fromℕ O n
coreH O .Handler.handle Plus     k = CoreOps._+_ O (k zero) (k (suc zero))
coreH O .Handler.handle Max      k = CoreOps._⊔_ O (k zero) (k (suc zero))
coreH O .Handler.handle (Pct p)  k = CoreOps.percentOf O p (k tt)
coreH O .Handler.respects Zero     e = refl
coreH O .Handler.respects (Lit n)  e = refl
coreH O .Handler.respects Plus     e = cong₂ (CoreOps._+_ O) (e zero) (e (suc zero))
coreH O .Handler.respects Max      e = cong₂ (CoreOps._⊔_ O) (e zero) (e (suc zero))
coreH O .Handler.respects (Pct p)  e = cong (CoreOps.percentOf O p) (e tt)

subH : ∀ {S} → SubOps S → Handler SubC S
subH O .Handler.handle Sub k   = SubOps._-_ O (k zero) (k (suc zero))
subH O .Handler.respects Sub e = cong₂ (SubOps._-_ O) (e zero) (e (suc zero))

-- the algebra of an `Ops` is the copairing of its layers' algebras
opsH : ∀ {S} → Ops S → Handler ExprC S
opsH O = coreH (Ops.core O) ⊕ subH (Ops.sub O)
