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

open import Level using (0ℓ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Container.Core using (Shape; Position; _▷_; _⇒_; shape; position)
open import Data.Container.Combinator using (_⊎_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
open import Function.Bundles using (_⟨$⟩_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; setoid)

open import Container.FreeMonad using (Eq; refl⋆; sym⋆; trans⋆; bind-cong; bind-pure; bind-assoc; fmap)
open import Container.Lowering using (translate)
open import Container.Sum using (inl; inr)

open import Slides.Diagram.Scalar using (Ops; CoreOps; SubOps; natOps; IsOpsHom)
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

private
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

evalWith-weakenCore : ∀ {V S} (O : Ops S) (ρ : V → S) (e : Term CoreC V) →
                      evalWith O ρ (weakenCore e) ≡ evalCore (Ops.core O) ρ e
evalWith-weakenCore O ρ e =
  trans (foldT-translate inl (opsH O) ρ e) (foldT-ext _ _ (λ s k → refl) ρ e)

evalWith-weakenSub : ∀ {V S} (O : Ops S) (ρ : V → S) (e : Term SubC V) →
                     evalWith O ρ (weakenSub e) ≡ evalSub (Ops.sub O) ρ e
evalWith-weakenSub O ρ e =
  trans (foldT-translate inr (opsH O) ρ e) (foldT-ext _ _ (λ s k → refl) ρ e)

------------------------------------------------------------------------
-- The `Ops` structure

exprOps : ∀ {V} → Ops (Expr V)
exprOps = record { core = termCore ; sub = termSub ; toℕ = eval (λ _ → 0) }

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
