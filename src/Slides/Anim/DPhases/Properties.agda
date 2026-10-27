{-# OPTIONS --safe --without-K #-}

-- The two readings of the shipped phases: `Slides.Anim.Phases.Properties.Over` at ℚ (continuous
-- templates) and at ℕ (discrete ones).
--
-- Continuous templates (`Slides.Anim.Phases.phasesOf`): the formulas are read in ℚ (`⟦_⟧`), the
-- symbolic coordinate is `Expr ℕ` evaluated in ℚ (`evalWith ratOps`), and the folds are exact
-- (`enc-sem`, `enc-num`).
--
-- Discrete templates (`Slides.Anim.DPhases.phasesOfD`): the formulas are read in ℕ with a real
-- half for the positions (`⟦_⟧ᴰ`), the symbolic coordinate is `DExpr ℕ` evaluated in ℕ (`evalD natD`),
-- and the folds are exact with no side condition (`encD-semN`, `enc-numN`).  The encoder never
-- produces a half except at the root (`encD-hlf`), so a slot that is not a position is read as its
-- value in ℕ (`val-nohlf`).
--
-- Each instance names its two facts (`slot-val`, `slot-num`) and then has `encode-sem` and
-- `pageFrame-sem` from the generic proof; `encodeDraw-sem`, `pageFrame-sem` (continuous) and
-- `encodeDrawD-sem`, `pageFrameD-sem` (discrete) are those theorems under their old names.

module Slides.Anim.DPhases.Properties where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (just; nothing)
open import Data.Nat as ℕ using (ℕ; _/_; _+_; _∸_; _⊔_)
open import Data.Fin using (zero) renaming (suc to fsuc)
open import Data.Container.FreeMonad using (pure; impure)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ)
open import Data.Integer using (+_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Slides.Diagram.Expr using (eval; evalWith)
import Slides.Diagram.Expr as E
open import Slides.Diagram.Euclid using (DExpr; evalD; natD)
import Slides.Diagram.Euclid as Eu
open import Slides.Diagram.NatQ using (ι)
open import Slides.Diagram.Scalar using (ratOps)
open import Slides.Anim.Formula
open import Slides.Anim.Formula.Properties
open import Slides.Anim.Phases
open import Slides.Anim.DPhases using (slotFD)
open import Slides.Anim.Phases.Properties

------------------------------------------------------------------------
-- Continuous templates, read in ℚ

private
  slot-valℚ : ∀ x ρ → ⟦ slotF x ⟧ ρ ≡ halfIf (proj₁ x) (evalWith ratOps ρ (proj₂ x))
  slot-valℚ (pos  , e) ρ = trans (half-sem (encE e) ρ) (cong ((+ 1 ℚ./ 2) ℚ.*_) (enc-semE e ρ))
  slot-valℚ (size , e) ρ = enc-semE e ρ

  -- a number that folded to a constant is the base number
  slot-numℚ : ∀ x c ρ → slotF x ≡ num c →
              baseNum (proj₁ x , eval (λ _ → 0) (proj₂ x)) ≡ halfIf (proj₁ x) (evalWith ratOps ρ (proj₂ x))
  slot-numℚ (pos , e) c ρ h with half-num-inv (encE e) c h
  ... | a , e₁ , refl =
    trans (cong (λ v → ι (v / 2)) (enc-numE e a e₁ (λ _ → 0)))
          (trans (cong (λ f → ⟦ f ⟧ ρ) (sym h)) (slot-valℚ (pos , e) ρ))
  slot-numℚ (size , e) c ρ h =
    trans (cong ι (enc-numE e c h (λ _ → 0)))
          (trans (cong (λ f → ⟦ f ⟧ ρ) (sym h)) (slot-valℚ (size , e) ρ))

module Continuous = Over slotF (eval (λ _ → 0)) (λ f ρ → ⟦ f ⟧ ρ) (λ ρ e → evalWith ratOps ρ e) slot-valℚ slot-numℚ

encodeDraw-sem = Continuous.encode-sem
pageFrame-sem  = Continuous.pageFrame-sem

------------------------------------------------------------------------
-- Discrete templates, read in ℕ

private
  -- the encoder never produces a half except at the root (`half`)
  foldOr-hlf : ∀ m g c → foldOr m g ≡ hlf c → g ≡ hlf c
  foldOr-hlf (just _) g c ()
  foldOr-hlf nothing  g c h = h

  fold1-hlf : ∀ f mk → (∀ a c → mk a ≡ hlf c → ⊥) → ∀ a c → fold1 f mk a ≡ hlf c → ⊥
  fold1-hlf f mk nn a c h = nn a c (foldOr-hlf _ (mk a) c h)

  fold2-hlf : ∀ f mk → (∀ a b c → mk a b ≡ hlf c → ⊥) → ∀ a b c → fold2 f mk a b ≡ hlf c → ⊥
  fold2-hlf f mk nn a b c h = nn a b c (foldOr-hlf _ (mk a b) c h)

  ltF-hlf : ∀ a b x y c → ltF a b x y ≡ hlf c → (x ≡ hlf c) ⊎ (y ≡ hlf c)
  ltF-hlf a b x y c h with numOf a | numOf b
  ltF-hlf a b x y c h | just u | just v with u ℕ.<ᵇ v
  ltF-hlf a b x y c h | just u | just v | true  = inj₁ h
  ltF-hlf a b x y c h | just u | just v | false = inj₂ h
  ltF-hlf a b x y c () | just _ | nothing
  ltF-hlf a b x y c () | nothing | _

encD-hlf : ∀ (e : DExpr ℕ) c → encD e ≡ hlf c → ⊥
encD-hlf (pure v) c ()
encD-hlf (impure (inj₁ (inj₁ E.Zero) , _)) c ()
encD-hlf (impure (inj₁ (inj₁ (E.Lit n)) , _)) c ()
encD-hlf (impure (inj₁ (inj₁ E.Plus) , k)) c h = fold2-hlf _ add (λ _ _ _ ()) (encD (k zero)) (encD (k (fsuc zero))) c h
encD-hlf (impure (inj₁ (inj₁ E.Max) , k)) c h = fold2-hlf _ max (λ _ _ _ ()) (encD (k zero)) (encD (k (fsuc zero))) c h
encD-hlf (impure (inj₁ (inj₁ (E.Pct p)) , k)) c h = fold1-hlf _ (pct p) (λ _ _ ()) (encD (k tt)) c h
encD-hlf (impure (inj₁ (inj₂ E.Sub) , k)) c h = fold2-hlf _ sub (λ _ _ _ ()) (encD (k zero)) (encD (k (fsuc zero))) c h
encD-hlf (impure (inj₂ (Eu.DivBy d) , k)) c h = fold1-hlf _ (fdiv d) (λ _ _ ()) (encD (k tt)) c h
encD-hlf (impure (inj₂ (Eu.ModBy d) , k)) c h = fold1-hlf _ (fmod d) (λ _ _ ()) (encD (k tt)) c h
encD-hlf (impure (inj₂ (Eu.MulLit n) , k)) c h = fold1-hlf _ (fmul n) (λ _ _ ()) (encD (k tt)) c h
encD-hlf (impure (inj₂ Eu.Lt , k)) c h with ltF-hlf (encD (k zero)) (encD (k (fsuc zero))) (encD (k (fsuc (fsuc zero)))) (encD (k (fsuc (fsuc (fsuc zero))))) c h
... | inj₁ hx = encD-hlf (k (fsuc (fsuc zero))) c hx
... | inj₂ hy = encD-hlf (k (fsuc (fsuc (fsuc zero)))) c hy

private
  -- a formula that is not a half is read as its value in ℕ
  -- a formula that is not a half is read as its value in ℕ
  val-nohlf : ∀ f ρ → (∀ c → f ≡ hlf c → ⊥) → ⟦ f ⟧ᴰ ρ ≡ ι (⟦ f ⟧ᴺ ρ)
  val-nohlf (num _)       ρ nn = refl
  val-nohlf (var _)       ρ nn = refl
  val-nohlf (add _ _)     ρ nn = refl
  val-nohlf (sub _ _)     ρ nn = refl
  val-nohlf (max _ _)     ρ nn = refl
  val-nohlf (pct _ _)     ρ nn = refl
  val-nohlf (hlf a)       ρ nn = ⊥-elim (nn a refl)
  val-nohlf (fdiv _ _)    ρ nn = refl
  val-nohlf (fmod _ _)    ρ nn = refl
  val-nohlf (fmul _ _)    ρ nn = refl
  val-nohlf (flt _ _ _ _) ρ nn = refl
  val-nohlf (fmin _ _)    ρ nn = refl
  val-nohlf (fease _ _)   ρ nn = refl

  slot-valℕ : ∀ x ρ → ⟦ slotFD x ⟧ᴰ ρ ≡ halfIf (proj₁ x) (ι (evalD natD ρ (proj₂ x)))
  slot-valℕ (pos  , e) ρ = trans (half-semN (encD e) ρ) (cong (λ v → (+ 1 ℚ./ 2) ℚ.* ι v) (encD-semN e ρ))
  slot-valℕ (size , e) ρ = trans (val-nohlf (encD e) ρ (encD-hlf e)) (cong ι (encD-semN e ρ))

  -- a number that folded to a constant is the base number
  slot-numℕ : ∀ x c ρ → slotFD x ≡ num c →
              baseNum (proj₁ x , evalD natD (λ _ → 0) (proj₂ x)) ≡ halfIf (proj₁ x) (ι (evalD natD ρ (proj₂ x)))
  slot-numℕ (pos , e) c ρ h with half-num-inv (encD e) c h
  ... | a , e₁ , refl =
    trans (cong (λ v → ι (v / 2)) (enc-numN e a e₁ (λ _ → 0)))
          (trans (cong (λ f → ⟦ f ⟧ᴰ ρ) (sym h)) (slot-valℕ (pos , e) ρ))
  slot-numℕ (size , e) c ρ h =
    trans (cong ι (enc-numN e c h (λ _ → 0)))
          (trans (cong (λ f → ⟦ f ⟧ᴰ ρ) (sym h)) (slot-valℕ (size , e) ρ))

module Discrete = Over slotFD (evalD natD (λ _ → 0)) (λ f ρ → ⟦ f ⟧ᴰ ρ) (λ ρ e → ι (evalD natD ρ e)) slot-valℕ slot-numℕ

encodeDrawD-sem = Discrete.encode-sem
pageFrameD-sem  = Discrete.pageFrame-sem
