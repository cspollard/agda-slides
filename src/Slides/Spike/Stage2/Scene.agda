{-# OPTIONS --safe --without-K #-}

-- STAGE 2 SPIKE (plan/Unify.md): the temporal container with the segment as a derived form,
-- and the embedding of the animation language into scenes.
--
--   TimeC    = Seq, Par (binary); Hold n, Delay n, Repeat n (unary); Drive tr (unary)
--   SceneC S = TimeC ⊎ DiagramC S           Scene S = SceneC S ⋆ ⊥     (as Spike.Timed)
--
-- Two additions to the Stage 0 container, both forced by the animation language:
--   * `Drive tr`: a *time-varying scalar*.  A template segment is a diagram over `Expr ⊤` whose one
--     variable is the segment's parameter; `Drive tr` binds that variable to the track's value at
--     the local time.  Semantically it is substitution along a signal (plan section 2.2): the
--     carrier is a reader `ℚ → X` and `Drive` is `bind`.
--   * `Repeat n`: n copies end to end, one child (the loop is not unrolled in the syntax).
--
-- A segment is `Hold n (Drive tr (inj d))`: `inj d` is the template as an eternal (duration 0)
-- constant, `Drive` makes it vary, `Hold` gives it the window [0, n).  The ℕ-valued duration is
-- the `Hold` count, so durations stay in `ℕ` (`dur` is unchanged).
--
-- Seq is guarded: `seqW x y = holdT (|x| + |y|) (seqAt x y)`.  `seqAt` alone shows its left
-- operand at negative times and its right operand beyond the end; for windowed operands
-- (everything under a `Hold`) the guard does nothing (`Properties.seqW-tick`), for the rest it
-- is the only lawful reading.

module Slides.Spike.Stage2.Scene where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Container.Core using (Container; _▷_; Shape; Position)
open import Data.Container.Combinator using (_⊎_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)

open import Slides.Diagram.Syntax
open import Slides.Diagram.Expr using (Expr; evalWith)
open import Slides.Diagram.Scalar using (ratOps)
open import Slides.Anim.Continuous using (Timed; seqAt; parAt; sampleAt; leafAt)
import Slides.Anim.Track as Tr
import Slides.Anim.Syntax as A
open import Slides.Spike.Timed using (TM; holdT; delayT; mapT; gather; fin2)

------------------------------------------------------------------------
-- The signature

data TOp : Set where
  Seq Par : TOp
  Hold Delay Repeat : ℕ → TOp
  Drive : Tr.Track ℚ → TOp

tarity : TOp → Set
tarity Seq        = Fin 2
tarity Par        = Fin 2
tarity (Hold _)   = ⊤
tarity (Delay _)  = ⊤
tarity (Repeat _) = ⊤
tarity (Drive _)  = ⊤

TimeC : Container 0ℓ 0ℓ
TimeC = TOp ▷ tarity

SceneC : Set → Container 0ℓ 0ℓ
SceneC S = TimeC ⊎ DiagramC S

Scene : Set → Set
Scene S = SceneC S ⋆ ⊥

-- a diagram is an eternal scene
inj : ∀ {S} → Dia S → Scene S
inj (pure ())
inj (impure (o , k)) = impure (inj₂ o , λ i → inj (k i))

------------------------------------------------------------------------
-- Set-level copairing (decision (c)): `Container.Sum.copair` is stated on setoid `Func`s and
-- needs a `cong` proof per summand; for a plain fold this is the whole of it.

cata : ∀ {C : Container 0ℓ 0ℓ} {X : Set} → ((s : Shape C) → (Position C s → X) → X) → C ⋆ ⊥ → X
cata a (pure ())
cata a (impure (s , k)) = a s (λ p → cata a (k p))

copairAlg : ∀ {C₁ C₂ : Container 0ℓ 0ℓ} {X : Set} →
  ((s : Shape C₁) → (Position C₁ s → X) → X) → ((s : Shape C₂) → (Position C₂ s → X) → X) →
  (s : Shape (C₁ ⊎ C₂)) → (Position (C₁ ⊎ C₂) s → X) → X
copairAlg a b (inj₁ s) k = a s k
copairAlg a b (inj₂ s) k = b s k

------------------------------------------------------------------------
-- The temporal algebra on `TM A = ℕ × (ℚ → Maybe A)`

-- sequencing, guarded to the window [0, |x| + |y|)
seqW : ∀ {A} → TM A → TM A → TM A
seqW x y = holdT (proj₁ x ℕ.+ proj₁ y) (seqAt x y)

-- n copies end to end
loopT : ∀ {A} → ℕ → TM A → TM A
loopT ℕ.zero    x = 0 , λ _ → nothing
loopT (ℕ.suc n) x = seqW x (loopT n x)

-- bind the parameter to a signal of local time (`bnd` is the carrier's substitution)
driveT : ∀ {A} → (ℚ → A → A) → (ℚ → ℚ) → TM A → TM A
driveT bnd w (n , f) = n , λ τ → Maybe.map (bnd (w τ)) (f τ)

timeAlg : ∀ {A} → (A → A → A) → (ℚ → A → A) → (s : Shape TimeC) → (Position TimeC s → TM A) → TM A
timeAlg ⊙ bnd Seq        k = seqW (k zero) (k (suc zero))
timeAlg ⊙ bnd Par        k = parAt ⊙ (k zero) (k (suc zero))
timeAlg ⊙ bnd (Hold n)   k = holdT n (k tt)
timeAlg ⊙ bnd (Delay n)  k = delayT n (k tt)
timeAlg ⊙ bnd (Repeat n) k = loopT n (k tt)
timeAlg ⊙ bnd (Drive tr) k = driveT bnd (proj₂ (sampleAt Tr.ℚLerp tr)) (k tt)

-- `α` interprets the diagram operations, `bnd` the substitution; `Par` overlays with `α Atop`
sceneAlg : ∀ {S A} → Algebra S A → (ℚ → A → A) → (s : Shape (SceneC S)) → (Position (SceneC S) s → TM A) → TM A
sceneAlg α bnd = copairAlg (timeAlg (λ x y → α Atop (fin2 x y)) bnd) (λ o k → gather o k (α o))

sample : ∀ {S A} → Algebra S A → (ℚ → A → A) → Scene S → TM A
sample α bnd = cata (sceneAlg α bnd)

------------------------------------------------------------------------
-- The reading in ℚ: frames as diagrams.  The carrier is a reader on the parameter.

RD : Set
RD = ℚ → Dia ℚ

algD : Algebra (Expr ⊤) RD
algD o k p = rescale (evalWith ratOps (λ _ → p)) o (λ i → k i p)

bindD : ℚ → RD → RD
bindD q g = λ _ → g q

-- the frames of a scene at time τ (the parameter is bound by `Drive`, so any value does)
framesD : Scene (Expr ⊤) → TM (Dia ℚ)
framesD s = mapT (λ g → g 0ℚ) (sample algD bindD s)

------------------------------------------------------------------------
-- The embedding of the animation language (template segments)

TSeg : Set
TSeg = Tr.Track ℚ × Dia (Expr ⊤)

TAnim : Set
TAnim = A.AnimC ⋆ TSeg

segS : TSeg → Scene (Expr ⊤)
segS (tr , d) = impure (inj₁ (Hold (Tr.dur tr)) , λ _ → impure (inj₁ (Drive tr) , λ _ → inj d))

embed : TAnim → Scene (Expr ⊤)
embed (pure s)                = segS s
embed (impure (A.Seq , k))    = impure (inj₁ Seq , λ i → embed (k i))
embed (impure (A.Par , k))    = impure (inj₁ Par , λ i → embed (k i))

-- the template-only animations of the existing library
toAnim : TAnim → A.Anim ℕ (A.Seg ℕ)
toAnim = A.foldA (λ { (tr , d) → pure (A.seg tr (A.template d)) }) A._⨾_ A._∥ᵃ_
