{-# OPTIONS --safe --without-K #-}

-- Laws of the ordered language: it is a free monad (substitution is `>>=`, the monad laws and
-- the fusion of evaluation with substitution are generic in the signature), evaluation is an
-- `Ops`-homomorphism (so layout is natural along it), the continuous templates embed, and
-- `Ease` is `Slides.Anim.Track.progress` with its end points, range and monotonicity.
module Slides.Spike.Ordered.Properties.Laws where

open import Data.Bool using (Bool; true; false; if_then_else_; T)
open import Data.Container.Core using (_⇒_; shape; position)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
open import Data.Product using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Sum.Base using (inj₁)
open import Data.Unit using (⊤; tt)
open import Data.Nat as ℕ using (ℕ)
import Data.Nat.DivMod as ℕDM
open import Relation.Binary.PropositionalEquality using (cong)
open import Slides.Diagram.NatQ using (ι)
open import Slides.Spike.Ordered.Properties using (ι-modBy)
open import Data.Product using (proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; setoid; subst)

open import Container.FreeMonad using (Eq)
open import Container.FreeMonad.Properties using (bind-pure; bind-assoc)
open import Container.Lowering using (translate)

open import Slides.Diagram.Scalar
open import Slides.Diagram.Signature
open import Slides.Diagram.Signature.Properties using (foldT-translate; foldT-ext)
open import Slides.Diagram.Expr using (Expr; ExprC; evalWith; opsH)
open import Slides.Anim.Track using (Easing; Linear; Step; StepStart; Bezier; progress; reverseE)
open import Slides.Anim.Track.Properties using (progress-0; progress-1; reversal; Exact)
open import Slides.Spike.Ordered

------------------------------------------------------------------------
-- (b) The ordered expressions are a free monad

-- substitution is the free monad's own bind (`Term QC V = QC ⋆ V`), so its laws are the
-- generic ones of `Container.FreeMonad.Properties`, at the sum container `QC`
QE : ∀ W → QExpr W → QExpr W → Set
QE W = Eq {C = QC} (setoid W)

qsubst-pure : ∀ {V} (e : QExpr V) → QE V (e >>= pure) e
qsubst-pure e = bind-pure (setoid _) e

qsubst-assoc : ∀ {U V W} (e : QExpr U) (σ : U → QExpr V) (τ : V → QExpr W) →
               QE W ((e >>= σ) >>= τ) (e >>= λ u → σ u >>= τ)
qsubst-assoc e σ τ = bind-assoc (setoid _) (setoid _) (setoid _) e σ τ

-- evaluation after substitution is evaluation with the evaluated substitution: ONE lemma, for any
-- signature and handler (it replaces `evalWith-subst`, `evalD-substD` and every future layer)
foldT-bind : ∀ {Σ V W S} (H : Handler Σ S) (ρ : W → S) (σ : V → Term Σ W) (e : Term Σ V) →
             foldT H ρ (e >>= σ) ≡ foldT H (λ v → foldT H ρ (σ v)) e
foldT-bind H ρ σ (pure v)         = refl
foldT-bind H ρ σ (impure (s , k)) = H .Handler.respects s (λ q → foldT-bind H ρ σ (k q))

------------------------------------------------------------------------
-- Layout is natural along evaluation

qexprOps : ∀ {V} → Ops (QExpr V)
qexprOps = record { core = termCoreQ ; sub = termSubQ ; toℕ = λ e → Ops.toℕ ratOps (evalQ ratQ (λ _ → 0ℚ) e) }

-- the evaluation into any `QOps` is an `Ops`-homomorphism, by construction: so
-- `Slides.Diagram.Layout.Properties.layout-natural` applies to it unchanged
evalQ-hom : ∀ {V S} (Q : QOps S) (ρ : V → S) → IsOpsHom qexprOps (QOps.ops Q) (evalQ Q ρ)
evalQ-hom Q ρ = record
  { coreHom = record
      { h-0 = refl ; h-+ = λ _ _ → refl ; h-⊔ = λ _ _ → refl ; h-fromℕ = λ _ → refl ; h-percentOf = λ _ _ → refl }
  ; subHom = record { h-- = λ _ _ → refl } }

------------------------------------------------------------------------
-- Continuous templates are ordered ones

exprQ : ExprC ⇒ QC
exprQ = record { shape = inj₁ ; position = λ q → q }

weakenQ : ∀ {V} → Expr V → QExpr V
weakenQ = translate exprQ

evalQ-weaken : ∀ {V S} (Q : QOps S) (ρ : V → S) (e : Expr V) →
               evalQ Q ρ (weakenQ e) ≡ evalWith (QOps.ops Q) ρ e
evalQ-weaken Q ρ e = trans (foldT-translate exprQ (qH Q) ρ e) (foldT-ext _ _ (λ s k → refl) ρ e)

------------------------------------------------------------------------
-- (c) Ease

-- `Ease` is `progress`, by definition
ease-progress : ∀ {V} (ρ : V → ℚ) e (a : QExpr V) → evalQ ratQ ρ (easeT e a) ≡ progress e (evalQ ratQ ρ a)
ease-progress ρ e a = refl

-- the end points: 0 ↦ 0 and 1 ↦ 1, for every easing
ease-0 : ∀ {V} (ρ : V → ℚ) e → evalQ ratQ ρ (easeT e zeroQ) ≡ 0ℚ
ease-0 ρ e = progress-0 e

ease-1 : ∀ {V} (ρ : V → ℚ) e → evalQ ratQ ρ (easeT e (litQ 1)) ≡ 1ℚ
ease-1 ρ e = progress-1 e

-- time reversal: `Ease e (1 − a) = 1 − Ease (reverseE e) a` (the easings that reverse exactly)
ease-reversal : ∀ {V} (ρ : V → ℚ) e → Exact e → (a : QExpr V) →
                evalQ ratQ ρ (easeT e (litQ 1 ⊖ᵠ a)) ≡ 1ℚ ℚ.- evalQ ratQ ρ (easeT (reverseE e) a)
ease-reversal ρ e ex a = reversal e ex (evalQ ratQ ρ a)

-- within [0, 1] (the player's progress on `[0, 1]`; a Bézier with a control point outside
-- [0, 100] overshoots on purpose, so there it holds only for control points in range: not proved)
InUnit : ℚ → Set
InUnit x = 0ℚ ≤ x × x ≤ 1ℚ

private
  0≤1 : 0ℚ ≤ 1ℚ
  0≤1 = ℚP.≤ᵇ⇒≤ {0ℚ} {1ℚ} tt

  bool-unit : ∀ b → InUnit (if b then 1ℚ else 0ℚ)
  bool-unit true  = 0≤1 , ℚP.≤-refl
  bool-unit false = ℚP.≤-refl , 0≤1

  bool-unit′ : ∀ b → InUnit (if b then 0ℚ else 1ℚ)
  bool-unit′ true  = ℚP.≤-refl , 0≤1
  bool-unit′ false = 0≤1 , ℚP.≤-refl

ease-range : ∀ e → Exact e → ∀ p → InUnit p → InUnit (progress e p)
ease-range Linear    _ p u = u
ease-range Step      _ p u = bool-unit (1ℚ ℚ.≤ᵇ p)
ease-range StepStart _ p u = bool-unit′ (p ℚ.≤ᵇ 0ℚ)
ease-range (Bezier _ _ _ _) ()

-- monotone, for the same easings
private
  step-mono : ∀ b c → (T b → T c) → (if b then 1ℚ else 0ℚ) ≤ (if c then 1ℚ else 0ℚ)
  step-mono true  true  _ = ℚP.≤-refl
  step-mono true  false f = ⊥-elim (f tt)
  step-mono false c     _ = proj₁ (bool-unit c)

  start-mono : ∀ b c → (T c → T b) → (if b then 0ℚ else 1ℚ) ≤ (if c then 0ℚ else 1ℚ)
  start-mono b false _ = proj₂ (bool-unit′ b)
  start-mono true  true _ = ℚP.≤-refl
  start-mono false true f = ⊥-elim (f tt)

ease-mono : ∀ e → Exact e → ∀ {p q} → p ≤ q → progress e p ≤ progress e q
ease-mono Linear    _ pq = pq
ease-mono Step      _ {p} {q} pq =
  step-mono (1ℚ ℚ.≤ᵇ p) (1ℚ ℚ.≤ᵇ q) (λ t → ℚP.≤⇒≤ᵇ (ℚP.≤-trans (ℚP.≤ᵇ⇒≤ {1ℚ} {p} t) pq))
ease-mono StepStart _ {p} {q} pq =
  start-mono (p ℚ.≤ᵇ 0ℚ) (q ℚ.≤ᵇ 0ℚ) (λ t → ℚP.≤⇒≤ᵇ (ℚP.≤-trans pq (ℚP.≤ᵇ⇒≤ {q} {0ℚ} t)))
ease-mono (Bezier _ _ _ _) ()

------------------------------------------------------------------------
-- Sample-and-hold and loops are time transformations (Kleisli substitution)

-- the whole tick of the time
holdT : QExpr ⊤
holdT = divByQ 0 tQ

-- A template held between ticks (the discrete reading of `Slides.Anim.Syntax.bodyAt`) is the
-- template composed with `τ ↦ ⌊τ⌋`: sampling `e >>= λ _ → holdT` at `q` is sampling `e` at `⌊q⌋`.
hold-law : ∀ {V} (e : QExpr V) (q : ℚ) →
           evalQ ratQ (λ _ → q) (e >>= λ _ → holdT) ≡ evalQ ratQ (λ _ → FloorOps.divBy ratFloor 0 q) e
hold-law e q = foldT-bind (qH ratQ) (λ _ → q) (λ _ → holdT) e

-- a loop of `n = d+1` frames is the template composed with `τ ↦ τ mod n`; on whole ticks it
-- is `n`-periodic (`Slides.Anim.Loop.phase-period`)
loopT : ℕ → QExpr ⊤
loopT d = modByQ d tQ

loop-period : ∀ d t → FloorOps.modBy ratFloor d (ι (t ℕ.+ ℕ.suc d)) ≡ FloorOps.modBy ratFloor d (ι t)
loop-period d t = trans (sym (ι-modBy d (t ℕ.+ ℕ.suc d)))
                 (trans (cong ι (ℕDM.[m+n]%n≡m%n t (ℕ.suc d))) (ι-modBy d t))
