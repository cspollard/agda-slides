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
--     `refl`).  `eval ρ` is the instance at ℕ.  It is the generic fold of
--     `Container.FreeMonad.Algebraic` (`Generic.fold-agrees`) and is unique among
--     `Ops`-homomorphisms (`evalWith-unique`);
--   * the monad laws of `Container.FreeMonad` hold for `subst` (`subst-bind`,
--     `subst-pure`, `subst-assoc`), in the free monad's own equality `Eq`.
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
open import Data.Container.Relation.Binary.Pointwise using () renaming (_,_ to _,ₚ_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; setoid)

open import Container.FreeMonad using (Eq; refl⋆; sym⋆; trans⋆; bind-cong; bind-pure; bind-assoc; fmap)
open import Container.FreeMonad.Algebraic using (module Alg)

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

------------------------------------------------------------------------
-- Substitution: the free monad's bind, as the fold into `exprOps`

-- (`subst-bind` below: it is also `_>>=_`, up to the free monad's own equality.)
-- `subst σ` is `evalWith exprOps σ`: the unique `Ops`-map that sends each variable `v` to
-- `σ v`.  So it is an `Ops`-homomorphism (`subst-hom`) on the nose, which is what lets
-- layout be natural along it (`Slides.Diagram.LayoutNatural`).
subst : ∀ {V W} → (V → Expr W) → Expr V → Expr W
subst σ = evalWith exprOps σ

rename : ∀ {V W} → (V → W) → Expr V → Expr W
rename f = subst (λ v → var (f v))

subst-hom : ∀ {V W} (σ : V → Expr W) → IsOpsHom exprOps exprOps (subst σ)
subst-hom σ = evalWith-hom exprOps σ

-- evaluating after substituting is evaluating with the evaluated substitution
evalWith-subst : ∀ {V W S} (O : Ops S) (ρ : W → S) (σ : V → Expr W) (e : Expr V) →
                 evalWith O ρ (subst σ e) ≡ evalWith O (λ v → evalWith O ρ (σ v)) e
evalWith-subst O ρ σ (pure v)                 = refl
evalWith-subst O ρ σ (impure (Zero , _))      = refl
evalWith-subst O ρ σ (impure (Lit n , _))     = refl
evalWith-subst O ρ σ (impure (Plus , k))      =
  cong₂ (Ops._+_ O) (evalWith-subst O ρ σ (k zero)) (evalWith-subst O ρ σ (k (suc zero)))
evalWith-subst O ρ σ (impure (Monus , k))     =
  cong₂ (Ops._-_ O) (evalWith-subst O ρ σ (k zero)) (evalWith-subst O ρ σ (k (suc zero)))
evalWith-subst O ρ σ (impure (Max , k))       =
  cong₂ (Ops._⊔_ O) (evalWith-subst O ρ σ (k zero)) (evalWith-subst O ρ σ (k (suc zero)))
evalWith-subst O ρ σ (impure (Pct p , k))     = cong (Ops.percentOf O p) (evalWith-subst O ρ σ (k tt))

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

-- `subst` is the free monad's bind
subst-bind : ∀ {V W} (σ : V → Expr W) (e : Expr V) → E W (subst σ e) (e >>= σ)
subst-bind σ (pure v)                = refl⋆ (setoid _) _
subst-bind σ (impure (Zero , k))     = refl , λ ()
subst-bind σ (impure (Lit n , k))    = refl , λ ()
subst-bind σ (impure (Plus , k))     = refl , λ { zero → subst-bind σ (k zero)
                                                ; (suc zero) → subst-bind σ (k (suc zero))
                                                ; (suc (suc ())) }
subst-bind σ (impure (Monus , k))    = refl , λ { zero → subst-bind σ (k zero)
                                                ; (suc zero) → subst-bind σ (k (suc zero))
                                                ; (suc (suc ())) }
subst-bind σ (impure (Max , k))      = refl , λ { zero → subst-bind σ (k zero)
                                                ; (suc zero) → subst-bind σ (k (suc zero))
                                                ; (suc (suc ())) }
subst-bind σ (impure (Pct p , k))    = refl , λ _ → subst-bind σ (k tt)

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
--
-- The handlers of an `Ops S` form an `ExprC`-algebra on `S`.  They only ever look at
-- finitely many children (arities are ⊥, ⊤ or `Fin 2`), so they respect pointwise-
-- equal children for `_≡_` itself, without function extensionality.

handle : ∀ {S} → Ops S → (o : ExprOp) → (exprArity o → S) → S
handle O Zero      k = Ops.0# O
handle O (Lit n)   k = Ops.fromℕ O n
handle O Plus      k = Ops._+_ O (k zero) (k (suc zero))
handle O Monus     k = Ops._-_ O (k zero) (k (suc zero))
handle O Max       k = Ops._⊔_ O (k zero) (k (suc zero))
handle O (Pct p)   k = Ops.percentOf O p (k tt)

handle-cong : ∀ {S} (O : Ops S) o {k k′ : exprArity o → S} →
              (∀ i → k i ≡ k′ i) → handle O o k ≡ handle O o k′
handle-cong O Zero      e = refl
handle-cong O (Lit n)   e = refl
handle-cong O Plus      e = cong₂ (Ops._+_ O) (e zero) (e (suc zero))
handle-cong O Monus     e = cong₂ (Ops._-_ O) (e zero) (e (suc zero))
handle-cong O Max       e = cong₂ (Ops._⊔_ O) (e zero) (e (suc zero))
handle-cong O (Pct p)   e = cong (Ops.percentOf O p) (e tt)

evalWith-handle : ∀ {V S} (O : Ops S) (ρ : V → S) o (k : exprArity o → Expr V) →
                  evalWith O ρ (impure (o , k)) ≡ handle O o (λ q → evalWith O ρ (k q))
evalWith-handle O ρ Zero     k = refl
evalWith-handle O ρ (Lit n)  k = refl
evalWith-handle O ρ Plus     k = refl
evalWith-handle O ρ Monus    k = refl
evalWith-handle O ρ Max      k = refl
evalWith-handle O ρ (Pct p)  k = refl

module Generic where
  module G = Alg 0ℓ 0ℓ ExprC
  open import Categories.Functor.Algebra using (F-Algebra)

  -- the `⟦ ExprC ⟧`-algebra of an `Ops S`, on the `≡`-setoid of `S`
  opsAlgebra : ∀ {S} → Ops S → F-Algebra G.F
  opsAlgebra {S} O = record
    { A = setoid S
    ; α = record
        { to   = λ { (o , k) → handle O o k }
        ; cong = λ { {_ , _} {_ , _} (refl ,ₚ k≈) → handle-cong O _ k≈ } } }

  -- an assignment, as a map out of the `≡`-setoid of the variables
  assign : ∀ {V S : Set} → (V → S) → Func (setoid V) (setoid S)
  assign ρ = record { to = ρ ; cong = cong ρ }

  -- the concrete fold is the generic one
  fold-agrees : ∀ {V S} (O : Ops S) (ρ : V → S) (e : Expr V) →
                G.fold (opsAlgebra O) (assign ρ) e ≡ evalWith O ρ e
  fold-agrees O ρ (pure v)      = refl
  fold-agrees O ρ (impure (o , k)) =
    sym (trans (evalWith-handle O ρ o k) (sym (handle-cong O o (λ i → fold-agrees O ρ (k i)))))

------------------------------------------------------------------------
-- Initiality: the free algebra's universal property
--
-- Any `Ops`-homomorphism out of `Expr V` is `evalWith` of its values on the variables.
-- (The homomorphism is assumed to respect `Eq` -- it cannot fail to, but showing
-- it needs function extensionality, since `a ⊞ b` presents its children as `pick2 a b`.)

evalWith-unique : ∀ {V S} (O : Ops S) (h : Expr V → S) → IsOpsHom exprOps O h →
                  (∀ {t u} → E V t u → h t ≡ h u) →
                  ∀ e → h e ≡ evalWith O (λ v → h (var v)) e
evalWith-unique O h hom ext (pure v)             = refl
evalWith-unique O h hom ext (impure (Zero , k))  =
  trans (ext (refl , λ ())) (IsOpsHom.h-0 hom)
evalWith-unique O h hom ext (impure (Lit n , k)) =
  trans (ext (refl , λ ())) (IsOpsHom.h-fromℕ hom n)
evalWith-unique {V} O h hom ext (impure (Plus , k)) =
  trans (ext (refl , two k))
 (trans (IsOpsHom.h-+ hom (k zero) (k (suc zero)))
        (cong₂ (Ops._+_ O) (evalWith-unique O h hom ext (k zero)) (evalWith-unique O h hom ext (k (suc zero)))))
  where two : ∀ (k : Fin 2 → Expr V) → ∀ q → E V (k q) (pick2 (k zero) (k (suc zero)) q)
        two k zero = refl⋆ (setoid V) _
        two k (suc zero) = refl⋆ (setoid V) _
        two k (suc (suc ()))
evalWith-unique {V} O h hom ext (impure (Monus , k)) =
  trans (ext (refl , two k))
 (trans (IsOpsHom.h-- hom (k zero) (k (suc zero)))
        (cong₂ (Ops._-_ O) (evalWith-unique O h hom ext (k zero)) (evalWith-unique O h hom ext (k (suc zero)))))
  where two : ∀ (k : Fin 2 → Expr V) → ∀ q → E V (k q) (pick2 (k zero) (k (suc zero)) q)
        two k zero = refl⋆ (setoid V) _
        two k (suc zero) = refl⋆ (setoid V) _
        two k (suc (suc ()))
evalWith-unique {V} O h hom ext (impure (Max , k)) =
  trans (ext (refl , two k))
 (trans (IsOpsHom.h-⊔ hom (k zero) (k (suc zero)))
        (cong₂ (Ops._⊔_ O) (evalWith-unique O h hom ext (k zero)) (evalWith-unique O h hom ext (k (suc zero)))))
  where two : ∀ (k : Fin 2 → Expr V) → ∀ q → E V (k q) (pick2 (k zero) (k (suc zero)) q)
        two k zero = refl⋆ (setoid V) _
        two k (suc zero) = refl⋆ (setoid V) _
        two k (suc (suc ()))
evalWith-unique {V} O h hom ext (impure (Pct p , k)) =
  trans (ext (refl , λ _ → refl⋆ (setoid V) _))
 (trans (IsOpsHom.h-percentOf hom p (k tt))
        (cong (Ops.percentOf O p) (evalWith-unique O h hom ext (k tt))))
