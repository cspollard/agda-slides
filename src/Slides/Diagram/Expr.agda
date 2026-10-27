{-# OPTIONS --safe --without-K #-}

-- Symbolic scalars: the free algebra of layered signatures.
--
-- A layout is computed in a scalar `Ops S` (`Slides.Diagram.Scalar`).  Take the scalar to
-- be an *expression*: the terms built from literals and the operations the layout uses,
-- over a set `V` of variables.  Those terms are the free monad on a container
-- (`Slides.Diagram.Signature`: `Term Σ V = Σ ⋆ V`), and the signature `Σ` is made of
-- *layers*, composed as a sum of containers (`Data.Container.Combinator._⊎_`):
--
--     CoreC = CoreOp ▷ coreArity     zero, literal `fromℕ n`, plus, max, `pct p`
--     SubC  = SubOp  ▷ subArity      sub  (monus in ℕ, real subtraction in ℤ, ℚ)
--     ExprC = CoreC ⊎ SubC           the signature of the layout's scalar
--
-- Each layer is interpreted by its own record of operations (`CoreOps`, `SubOps`), and
-- the interpretation of a sum is the copairing of the two (`Signature._⊕_`, which is
-- `Container.Sum.copair`).  `Expr V = Term ExprC V` is what the rest of the library uses:
--
--   * `Expr V` is an `Ops` (`exprOps`: the operations are the constructors, with `0#` the
--     zero): laying a diagram out *in* `Expr V` leaves every coordinate as a formula,
--     computed once;
--   * `>>=` is substitution (`rename`, `subst`), `pure` a variable;
--   * `evalWith O ρ : Expr V → S` is the fold, the unique `Ops`-map extending an
--     assignment `ρ : V → S` (the free algebra's universal property), and it is an
--     `Ops`-homomorphism by construction (`evalWith-hom`, equalities of the form `refl`;
--     one `IsCoreHom` and one `IsSubHom`).  `eval ρ` is the instance at ℕ.  It is the
--     generic fold of `Container.FreeMonad.Algebraic` (`Signature.Generic.fold-agrees`)
--     and is unique among `Ops`-homomorphisms (`evalWith-unique`);
--   * a term over one layer is a term over the sum, along the inclusion
--     (`weakenCore`, `weakenSub`: translation along `inl`, `inr`, a monad morphism,
--     `Signature.weaken-bind`), and evaluating the weakened term needs only that layer's
--     operations (`evalWith-weakenCore`, `evalWith-weakenSub`).  A signature with a
--     further layer (`Slides.Diagram.Euclid`) is another sum; terms that do not mention
--     it are terms over this one;
--   * the monad laws of `Container.FreeMonad` hold for `subst` (`subst-bind`,
--     `subst-pure`, `subst-assoc`), in the free monad's own equality `Eq`.
--
-- The smart constructors (`zero′`, `lit`, `_⊞_`, `_⊓_`, `pct`; `_⊖_`) are written once
-- for any signature with a container morphism from the layer (`CoreSyntax`,
-- `SubSyntax`), and `Expr`'s are the instances at `inl`, `inr`.
--
-- A template body of an animation (`Slides.Anim.Syntax`) has one variable, the segment's
-- parameter (`t : Expr ⊤`); a whole animation has one variable per segment, so that
-- segments played together keep independent parameters.
--
-- `toℕ` has no meaning for a formula; `exprOps` takes the value at the all-zero
-- assignment.  It is not part of `IsOpsHom` and layout never applies it.

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

Expr : Set → Set
Expr V = Term ExprC V

-- the two children of a binary node, as a function of the position (public: the laws in
-- `Slides.Diagram.Expr.Properties` state their equations with it)
pick2 : ∀ {A : Set} → A → A → Fin 2 → A
pick2 a b zero          = a
pick2 a b (suc zero)    = b
pick2 a b (suc (suc ()))

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

open CoreSyntax (inl {C₁ = CoreC} {C₂ = SubC}) public
open SubSyntax (inr {C₁ = CoreC} {C₂ = SubC}) public

var : ∀ {V} → V → Expr V
var = pure

-- the parameter of a template
t : Expr ⊤
t = pure tt

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

------------------------------------------------------------------------
-- Evaluation: the fold, into any scalar

evalWith : ∀ {V S} → Ops S → (V → S) → Expr V → S
evalWith O = foldT (opsH O)

-- at the naturals
eval : ∀ {V} → (V → ℕ) → Expr V → ℕ
eval = evalWith natOps

-- a term over one layer, evaluated with that layer's operations only
evalCore : ∀ {V S} → CoreOps S → (V → S) → Term CoreC V → S
evalCore O = foldT (coreH O)

evalSub : ∀ {V S} → SubOps S → (V → S) → Term SubC V → S
evalSub O = foldT (subH O)

------------------------------------------------------------------------
-- Inclusions of layers

weakenCore : ∀ {V} → Term CoreC V → Expr V
weakenCore = translate inl

weakenSub : ∀ {V} → Term SubC V → Expr V
weakenSub = translate inr

------------------------------------------------------------------------
-- The `Ops` structure

exprOps : ∀ {V} → Ops (Expr V)
exprOps = record { core = termCore ; sub = termSub ; toℕ = eval (λ _ → 0) }

------------------------------------------------------------------------
-- Substitution: the free monad's bind, as the fold into `exprOps`

-- (`subst-bind` below: it is also `_>>=_`, up to the free monad's own equality.)
-- `subst σ` is `evalWith exprOps σ`: the unique `Ops`-map that sends each variable `v` to
-- `σ v`.  So it is an `Ops`-homomorphism (`subst-hom`) on the nose, which is what lets
-- layout be natural along it (`Slides.Diagram.Layout.Properties`).
subst : ∀ {V W} → (V → Expr W) → Expr V → Expr W
subst σ = evalWith exprOps σ

rename : ∀ {V W} → (V → W) → Expr V → Expr W
rename f = subst (λ v → var (f v))
