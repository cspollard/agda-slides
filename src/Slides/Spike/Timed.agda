{-# OPTIONS --safe --without-K #-}

-- STAGE 0 SPIKE (plan/Unify.md): the temporal container and the pointwise lift.
--
--   TimeC    = Seq, Par (binary), Hold n, Delay n (unary)
--   SceneC S = TimeC ⊎ DiagramC S                (Data.Container.Combinator._⊎_)
--   Scene S  = SceneC S ⋆ ⊥
--
-- Why `⋆ ⊥` and not a leaf-carrying `SceneC S ⋆ L`: the primitives (rectangle, text, ...) are
-- already the nullary operations of `DiagramC S`, so a scene has no use for external leaves.
-- A leaf type `L` would need a semantics `L → Timed _` that every statement carries as a
-- hypothesis, and would duplicate the primitives.  Temporal extent comes from the one unary
-- operation `Hold n` (present exactly on [0, n)); a bare primitive is *eternal*: present at
-- every time, duration 0 (the unit of ⊔).
--
-- Absence (the key question).  The carrier is `TM A = Timed (Maybe A)`.
--   * temporal operations introduce and resolve absence: `Hold`/`Delay` create it, `Seq` is
--     `seqAt`, `Par` is `parAt` with the *unit-less* merge (`mergeM`, absence is the unit);
--   * spatial operations are the Maybe-applicative lift, STRICT: `op x y` is present iff every
--     child is present, and then it is `α op (x, y)`.  Duration is the maximum.  This needs no
--     law of `α` (no unit element for Beside/Above/...), so the lift works for every algebra.
--   `Par` is the only place where "absent child = erased" is used, and it is a *temporal* op
--   whose operation is Atop, defined from the algebra itself (`α Atop`).  Lenient lifting of
--   the other spatial ops is not lawful: see `Properties.overlay-no-unit`.

module Slides.Spike.Timed where

open import Level using (0ℓ)
open import Data.Bool using (Bool; _∧_; if_then_else_)
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

open import Slides.Diagram.NatQ using (ι)
open import Slides.Diagram.Syntax
open import Slides.Anim.Continuous using (Timed; seqAt; parAt; _<ᵗ_)

------------------------------------------------------------------------
-- The signature

data TOp : Set where
  Seq Par : TOp
  Hold Delay : ℕ → TOp

tarity : TOp → Set
tarity Seq       = Fin 2
tarity Par       = Fin 2
tarity (Hold _)  = ⊤
tarity (Delay _) = ⊤

TimeC : Container 0ℓ 0ℓ
TimeC = TOp ▷ tarity

SceneC : Set → Container 0ℓ 0ℓ
SceneC S = TimeC ⊎ DiagramC S

Scene : Set → Set
Scene S = SceneC S ⋆ ⊥

cata : ∀ {C : Container 0ℓ 0ℓ} {X : Set} → ((s : Shape C) → (Position C s → X) → X) → C ⋆ ⊥ → X
cata a (pure ())
cata a (impure (s , k)) = a s (λ p → cata a (k p))

------------------------------------------------------------------------
-- The carrier and the pointwise lift

TM : Set → Set
TM A = Timed (Maybe A)

mapT : ∀ {A B} → (A → B) → TM A → TM B
mapT h (n , f) = n , λ τ → Maybe.map h (f τ)

-- present on [0, n) only, as long as n
holdT : ∀ {A} → ℕ → TM A → TM A
holdT n (_ , f) = n , λ τ → if (0ℚ ℚ.≤ᵇ τ) ∧ (τ <ᵗ ι n) then f τ else nothing

-- start n ticks later
delayT : ∀ {A} → ℕ → TM A → TM A
delayT n (m , f) = n ℕ.+ m , λ τ → if τ <ᵗ ι n then nothing else f (τ ℚ.- ι n)

-- the Maybe applicative, strict: present iff both are
zipM : ∀ {A B C : Set} → (A → B → C) → Maybe A → Maybe B → Maybe C
zipM h (just x) (just y) = just (h x y)
zipM h _        _        = nothing

zipT : ∀ {A B C} → (A → B → C) → TM A → TM B → TM C
zipT h (n , f) (m , g) = n ℕ.⊔ m , λ τ → zipM h (f τ) (g τ)

-- an eternal constant
unitT : ∀ {A} → A → TM A
unitT a = 0 , λ _ → just a

fin2 : ∀ {A : Set} → A → A → Fin 2 → A
fin2 a b zero          = a
fin2 a b (suc zero)    = b
fin2 a b (suc (suc ()))

-- the strict pointwise lift of one spatial operation: `f` is the algebra's operation
gather : ∀ {S A B} (o : Op S) → (arity o → TM A) → ((arity o → A) → B) → TM B
gather (Rectangle _ _ _)    k f = unitT (f (λ ()))
gather (Disc _ _)           k f = unitT (f (λ ()))
gather (Segment _ _ _)      k f = unitT (f (λ ()))
gather (Text _ _ _ _)       k f = unitT (f (λ ()))
gather (Spacer _ _)         k f = unitT (f (λ ()))
gather (Beside _)           k f = zipT (λ x y → f (fin2 x y)) (k zero) (k (suc zero))
gather (Above _)            k f = zipT (λ x y → f (fin2 x y)) (k zero) (k (suc zero))
gather Atop                 k f = zipT (λ x y → f (fin2 x y)) (k zero) (k (suc zero))
gather LabelAbove           k f = zipT (λ x y → f (fin2 x y)) (k zero) (k (suc zero))
gather LabelBelow           k f = zipT (λ x y → f (fin2 x y)) (k zero) (k (suc zero))
gather (Place _ _ _ _)      k f = mapT (λ x → f (λ _ → x)) (k tt)
gather (Overlay _ _)        k f = zipT (λ x y → f (fin2 x y)) (k zero) (k (suc zero))
gather (Named _)            k f = mapT (λ x → f (λ _ → x)) (k tt)
gather (Connect _ _ _ _ _)  k f = mapT (λ x → f (λ _ → x)) (k tt)

-- the algebra of scenes into `TM A`, from an algebra of diagrams; Par overlays with its Atop
sceneAlg : ∀ {S A} → Algebra S A → (s : Shape (SceneC S)) → (Position (SceneC S) s → TM A) → TM A
sceneAlg α (inj₁ Seq)       k = seqAt (k zero) (k (suc zero))
sceneAlg α (inj₁ Par)       k = parAt (λ x y → α Atop (fin2 x y)) (k zero) (k (suc zero))
sceneAlg α (inj₁ (Hold n))  k = holdT n (k tt)
sceneAlg α (inj₁ (Delay n)) k = delayT n (k tt)
sceneAlg α (inj₂ o)         k = gather o k (α o)

-- the term algebra: the carrier is the diagram itself
con : ∀ {S} → Algebra S (Dia S)
con o k = impure (o , k)

sample : ∀ {S A} → Algebra S A → Scene S → TM A
sample α = cata (sceneAlg α)

-- `restrict t τ`: the diagram that the scene shows at time τ
restrict : ∀ {S} → Scene S → ℚ → Maybe (Dia S)
restrict t τ = proj₂ (sample con t) τ
