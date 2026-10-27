{-# OPTIONS --safe --without-K #-}

-- Laws of the ordered language.  Layers used per lemma: the monad laws, `foldT-bind`, `foldT-lower`,
-- `evalQ-hom`, `evalQ-weaken` and `hold-law` are generic (any signature, any `QOps S`, no law);
-- `modByQ-def`, `minQ-def` use Floor + Sub and Ord and the laws `QLaws` of the model;
-- `ease-*` use Ease and are about ℚ (`Slides.Anim.Track.progress`); `loop-period` uses Floor,
-- with ℕ ticks read through `ι`.
module Slides.Diagram.Ordered.Properties.Laws where

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
open import Slides.Diagram.Ordered.Properties using (ι-modBy)
open import Data.Product using (proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; setoid; subst)

open import Container.FreeMonad using (Eq)
open import Container.FreeMonad.Properties using (bind-pure; bind-assoc)
open import Container.Lowering using (Lowering; lower; translate)

open import Slides.Diagram.Scalar
open import Slides.Diagram.Signature
open import Slides.Diagram.Signature.Properties using (foldT-translate; foldT-ext)
open import Slides.Diagram.Expr using (Expr; ExprC; evalWith; opsH)
open import Slides.Anim.Track using (Easing; Linear; Step; StepStart; Bezier; progress; reverseE)
open import Slides.Anim.Track.Properties using (progress-0; progress-1; reversal; Exact)
open import Slides.Diagram.Ordered

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

-- the fold depends on the assignment only pointwise
foldT-cong : ∀ {Σ V S} (H : Handler Σ S) {ρ ρ′ : V → S} → (∀ v → ρ v ≡ ρ′ v) → (e : Term Σ V) →
             foldT H ρ e ≡ foldT H ρ′ e
foldT-cong H h (pure v)         = h v
foldT-cong H h (impure (s , k)) = H .Handler.respects s (λ q → foldT-cong H h (k q))

-- fusion for a lowering (`Container.Lowering.lower-fusion`, concretely): folding a lowered term is
-- folding the original with the handler pulled back along the lowering
pull : ∀ {Σ Σ′ S} → Lowering Σ Σ′ → Handler Σ′ S → Handler Σ S
pull l H .Handler.handle s k   = foldT H k (l s)
pull l H .Handler.respects s e = foldT-cong H e (l s)

foldT-lower : ∀ {Σ Σ′ V S} (l : Lowering Σ Σ′) (H : Handler Σ′ S) (ρ : V → S) (e : Term Σ V) →
              foldT H ρ (lower l e) ≡ foldT (pull l H) ρ e
foldT-lower l H ρ (pure v)         = refl
foldT-lower l H ρ (impure (s , k)) =
  trans (foldT-bind H ρ (λ q → lower l (k q)) (l s))
        (foldT-cong H (λ q → foldT-lower l H ρ (k q)) (l s))

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

------------------------------------------------------------------------
-- `ModBy` and `Min` are the derived nodes the laws of a model say they are

modByQ-def : ∀ {V S} (Q : QOps S) → QLaws Q → (ρ : V → S) (d : ℕ) (e : QExpr V) →
             evalQ Q ρ (modByQ d e) ≡ evalQ Q ρ (e ⊖ᵠ mulLitQ (ℕ.suc d) (divByQ d e))
modByQ-def Q L ρ d e = QLaws.modBy-spec L d (evalQ Q ρ e)

minQ-def : ∀ {V S} (Q : QOps S) → QLaws Q → (ρ : V → S) (a b : QExpr V) →
           evalQ Q ρ (minQ a b) ≡ evalQ Q ρ (ltQ a b a b)
minQ-def Q L ρ a b = QLaws.min-spec L (evalQ Q ρ a) (evalQ Q ρ b)

------------------------------------------------------------------------
-- Sample-and-hold and loops are time transformations (Kleisli substitution)

-- the whole tick of the time
holdT : QExpr ⊤
holdT = divByQ 0 tQ

-- A template held between ticks (the discrete reading of `Slides.Anim.Syntax.bodyAt`) is the
-- template composed with `τ ↦ ⌊τ⌋`: sampling `e >>= λ _ → holdT` at `q` is sampling `e` at `⌊q⌋`.
hold-law : ∀ {V S} (Q : QOps S) (e : QExpr V) (q : S) →
           evalQ Q (λ _ → q) (e >>= λ _ → holdT) ≡ evalQ Q (λ _ → FloorOps.divBy (QOps.floor Q) 0 q) e
hold-law Q e q = foldT-bind (qH Q) (λ _ → q) (λ _ → holdT) e

-- a loop of `n = d+1` frames is the template composed with `τ ↦ τ mod n`; on whole ticks it
-- is `n`-periodic (`Slides.Anim.Loop.phase-period`)
loopT : ℕ → QExpr ⊤
loopT d = modByQ d tQ

loop-period : ∀ d t → FloorOps.modBy ratFloor d (ι (t ℕ.+ ℕ.suc d)) ≡ FloorOps.modBy ratFloor d (ι t)
loop-period d t = trans (sym (ι-modBy d (t ℕ.+ ℕ.suc d)))
                 (trans (cong ι (ℕDM.[m+n]%n≡m%n t (ℕ.suc d))) (ι-modBy d t))
