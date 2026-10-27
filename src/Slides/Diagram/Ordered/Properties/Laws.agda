{-# OPTIONS --safe --without-K #-}

-- Laws of the ordered language.  Layers used per lemma: `foldT-bind`, `foldT-lower`, `evalO-hom`,
-- `evalO-weaken` and `hold-law` are generic (any signature, any `OOps S`, no law); `modByQ-def`,
-- `minQ-def` use Floor + Sub and Ord and the laws `QLaws` of the model; `ease-*` use Ease and are
-- about ℚ (`Slides.Anim.Track.progress`); `loop-period` uses Floor, with ℕ ticks read through `ι`.
--
-- The monad laws of the free monad (`OExpr V = OC ⋆ V`, substitution is `_>>=_`) are the generic ones
-- of `Container.FreeMonad.Properties` and are not restated.
module Slides.Diagram.Ordered.Properties.Laws where

open import Data.Container.Core using (_⇒_; shape; position; Shape; Position)
open import Data.Container.FreeMonad using (pure; impure; _>>=_)
open import Data.Product using (_,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Nat as ℕ using (ℕ)
import Data.Nat.DivMod as ℕDM
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Container.Lowering using (Lowering; lower; translate)
open import Container.Sum using (inl)

open import Slides.Diagram.NatQ using (ι)
open import Slides.Diagram.Draw using (mapLayout)
open import Slides.Diagram.Syntax using (Dia; mapDia)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Slides.Diagram.Layout.Properties using (layout-natural; mapLayout-∘; mapLayout-cong)
open import Slides.Diagram.Scalar
open import Slides.Diagram.Signature
open import Slides.Diagram.Signature.Properties using (foldT-translate; foldT-ext)
open import Slides.Diagram.Expr using (Zero; Lit; Plus; Max; Pct; Sub)
open import Slides.Anim.Track using (Easing; progress; reverseE)
open import Slides.Anim.Track.Properties using (progress-0; progress-1; reversal; Exact)
open import Slides.Diagram.Ordered
open import Slides.Diagram.Ordered.Properties using (ι-modBy; IsOrdHom; IsFloorHom)

------------------------------------------------------------------------
-- Substitution and lowering fuse with evaluation

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

-- the evaluation into any `OOps` is an `Ops`-homomorphism, by construction: so
-- `Slides.Diagram.Layout.Properties.layout-natural` applies to it unchanged
evalO-hom : ∀ {V S} (O : OOps S) (ρ : V → S) → IsOpsHom (OOps.ops termO) (OOps.ops O) (evalO O ρ)
evalO-hom O ρ = record
  { coreHom = record
      { h-0 = refl ; h-+ = λ _ _ → refl ; h-⊔ = λ _ _ → refl ; h-fromℕ = λ _ → refl ; h-percentOf = λ _ _ → refl }
  ; subHom = record { h-- = λ _ _ → refl } }

-- ... and of the ordered and floor layers
evalO-ord-hom : ∀ {V S} (O : OOps S) (ρ : V → S) → IsOrdHom (OOps.ord termO) (OOps.ord O) (evalO O ρ)
evalO-ord-hom O ρ = record { h-lt = λ _ _ _ _ → refl ; h-min = λ _ _ → refl }

evalO-floor-hom : ∀ {V S} (O : OOps S) (ρ : V → S) → IsFloorHom (OOps.floor termO) (OOps.floor O) (evalO O ρ)
evalO-floor-hom O ρ = record { h-divBy = λ _ _ → refl ; h-modBy = λ _ _ → refl ; h-mulLit = λ _ _ → refl }

-- the evaluation into any `OOps` also commutes with the handler of a node, node by node
nodeO : ∀ {W S} (O : OOps S) (ρ : W → S) (s : Shape OC) (k : Position OC s → OExpr W) →
        evalO O ρ (oH termO .Handler.handle s k) ≡ oH O .Handler.handle s (λ q → evalO O ρ (k q))
nodeO O ρ (inj₁ (inj₁ Zero))    k = refl
nodeO O ρ (inj₁ (inj₁ (Lit n))) k = refl
nodeO O ρ (inj₁ (inj₁ Plus))    k = refl
nodeO O ρ (inj₁ (inj₁ Max))     k = refl
nodeO O ρ (inj₁ (inj₁ (Pct p))) k = refl
nodeO O ρ (inj₁ (inj₂ Sub))     k = refl
nodeO O ρ (inj₂ (inj₁ Lt))      k = refl
nodeO O ρ (inj₂ (inj₁ Min))     k = refl
nodeO O ρ (inj₂ (inj₂ (DivBy d)))  k = refl
nodeO O ρ (inj₂ (inj₂ (ModBy d)))  k = refl
nodeO O ρ (inj₂ (inj₂ (MulLit n))) k = refl

evalO-substO : ∀ {V W S} (O : OOps S) (ρ : W → S) (σ : V → OExpr W) (e : OExpr V) →
               evalO O ρ (substO σ e) ≡ evalO O (λ v → evalO O ρ (σ v)) e
evalO-substO O ρ σ (pure v)         = refl
evalO-substO O ρ σ (impure (s , k)) =
  trans (nodeO O ρ s (λ q → substO σ (k q))) (oH O .Handler.respects s (λ q → evalO-substO O ρ σ (k q)))

-- a diagram over symbolic sizes, laid out symbolically and evaluated, is the layout of the diagram
-- with the sizes evaluated; and laying out a template whose variable is replaced by formulas, evaluated
-- at `ρ`, is laying it out at the evaluated substitution
layout-evalO : ∀ {V S} (O : OOps S) (ρ : V → S) (d : Dia (OExpr V)) →
  mapLayout (evalO O ρ) (LayoutWith.layout termOps d) ≡ LayoutWith.layout (OOps.ops O) (mapDia (evalO O ρ) d)
layout-evalO O ρ = layout-natural termOps (OOps.ops O) (evalO O ρ) (evalO-hom O ρ)

layout-substO : ∀ {V W S} (O : OOps S) (σ : V → OExpr W) (ρ : W → S) (d : Dia (OExpr V)) →
  LayoutWith.layout (OOps.ops O) (mapDia (evalO O ρ) (mapDia (substO σ) d))
  ≡ LayoutWith.layout (OOps.ops O) (mapDia (evalO O (λ v → evalO O ρ (σ v))) d)
layout-substO O σ ρ d =
  trans (sym (layout-evalO O ρ (mapDia (substO σ) d)))
  (trans (cong (mapLayout (evalO O ρ)) (sym (layout-natural termOps termOps (substO σ) (evalO-hom termO σ) d)))
  (trans (mapLayout-∘ (evalO O ρ) (substO σ) (LayoutWith.layout termOps d))
  (trans (mapLayout-cong (evalO-substO O ρ σ) (LayoutWith.layout termOps d))
         (layout-evalO O (λ v → evalO O ρ (σ v)) d))))

------------------------------------------------------------------------
-- Terms of the larger signature

evalQ-weaken : ∀ {V S} (Q : QOps S) (ρ : V → S) (e : OExpr V) → evalQ Q ρ (weakenQ e) ≡ evalO (QOps.o Q) ρ e
evalQ-weaken Q ρ e = trans (foldT-translate inl (qH Q) ρ e) (foldT-ext _ _ (λ s k → refl) ρ e)

------------------------------------------------------------------------
-- `ModBy` and `Min` are the derived nodes the laws of a model say they are

modByQ-def : ∀ {V S} (O : OOps S) → QLaws O → (ρ : V → S) (d : ℕ) (e : OExpr V) →
             evalO O ρ (modBy d e) ≡ evalO O ρ (e ⊖ mulLit (ℕ.suc d) (divBy d e))
modByQ-def O L ρ d e = QLaws.modBy-spec L d (evalO O ρ e)

minQ-def : ∀ {V S} (O : OOps S) → QLaws O → (ρ : V → S) (a b : OExpr V) →
           evalO O ρ (minT a b) ≡ evalO O ρ (ltT a b a b)
minQ-def O L ρ a b = QLaws.min-spec L (evalO O ρ a) (evalO O ρ b)

------------------------------------------------------------------------
-- Ease

-- `Ease` is `progress`, by definition
ease-progress : ∀ {V} (ρ : V → ℚ) e (a : QExpr V) → evalQ ratQ ρ (easeT e a) ≡ progress e (evalQ ratQ ρ a)
ease-progress ρ e a = refl

-- the end points: 0 ↦ 0 and 1 ↦ 1, for every easing
ease-0 : ∀ {V} (ρ : V → ℚ) e → evalQ ratQ ρ (easeT e (weakenQ zero′)) ≡ 0ℚ
ease-0 ρ e = progress-0 e

ease-1 : ∀ {V} (ρ : V → ℚ) e → evalQ ratQ ρ (easeT e (weakenQ (lit 1))) ≡ 1ℚ
ease-1 ρ e = progress-1 e

-- time reversal: `Ease e (1 − a) = 1 − Ease (reverseE e) a` (the easings that reverse exactly)
ease-reversal : ∀ {V} (ρ : V → ℚ) e → Exact e → (a : OExpr V) →
                evalQ ratQ ρ (easeT e (weakenQ (lit 1 ⊖ a))) ≡ 1ℚ ℚ.- evalQ ratQ ρ (easeT (reverseE e) (weakenQ a))
ease-reversal ρ e ex a =
  trans (cong (progress e) (evalQ-weaken ratQ ρ (lit 1 ⊖ a)))
 (trans (reversal e ex (evalO ratO ρ a))
        (cong (λ x → 1ℚ ℚ.- progress (reverseE e) x) (sym (evalQ-weaken ratQ ρ a))))

------------------------------------------------------------------------
-- Sample-and-hold and loops are time transformations (Kleisli substitution)

-- A template held between ticks (the discrete reading of `Slides.Anim.Syntax.bodyAt`) is the
-- template composed with `τ ↦ ⌊τ⌋`: sampling `e >>= λ _ → holdT` at `q` is sampling `e` at `⌊q⌋`.
hold-law : ∀ {V S} (O : OOps S) (e : OExpr V) (q : S) →
           evalO O (λ _ → q) (e >>= λ _ → holdT) ≡ evalO O (λ _ → FloorOps.divBy (OOps.floor O) 0 q) e
hold-law O e q = foldT-bind (oH O) (λ _ → q) (λ _ → holdT) e

-- a loop of `n = d+1` frames is the template composed with `τ ↦ τ mod n`; on whole ticks it
-- is `n`-periodic (`Slides.Anim.Loop.phase-period`)
loopT : ℕ → OExpr ⊤
loopT d = modBy d tO

loop-period : ∀ d t → FloorOps.modBy ratFloor d (ι (t ℕ.+ ℕ.suc d)) ≡ FloorOps.modBy ratFloor d (ι t)
loop-period d t = trans (sym (ι-modBy d (t ℕ.+ ℕ.suc d)))
                 (trans (cong ι (ℕDM.[m+n]%n≡m%n t (ℕ.suc d))) (ι-modBy d t))
