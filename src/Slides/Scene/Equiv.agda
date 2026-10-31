{-# OPTIONS --safe --without-K #-}

-- Equality of scenes: `_≈ₛ_` is a setoid, the signature is congruent for it, and the laws of
-- Hudak's temporal media (*An algebraic theory of polymorphic temporal media*, 2004) are
-- equations in it.
--
--   `a ≈ₛ b`   whatever the leaves read, equal durations and pointwise equal readings
--   `sceneSetoid`, `impure-cong`   a setoid on scenes, and every operation respects it
--
--   par-assoc, par-comm, par-gap      `∥` is associative, commutative (if `⊙` is), absence its unit
--   seq-assoc                         `⨾` is associative
--   delay-delay, delay-zero           delays add, a zero delay is the identity
--   hold-hold                         a narrower window inside a wider one is the narrow window
--   hold-par, delay-par, drive-par    `hold`, `delay` and `drive` distribute over `∥`
--
-- Not claimed.  The unit of `⨾`: `hold 0 s ⨾ b ≈ b` only for `b` already windowed (a leaf is
-- eternal, `hold 0 s ⨾ leaf` shows nothing).  `hold a (hold b s) = hold (min a b) s`: `hold` has
-- the duration it was given, so this holds for `a ≤ b` only.  The swap law (see `Laws`).

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Slides.Scalar.Core using (OrdMon; Sub)
open import Slides.Diagram.Overlay using (Overlays)

module Slides.Scene.Equiv {T D X : Set} (M : OrdMon T) (Sb : Sub M) (val : D → T → T) (O : Overlays X) where

open import Level using (0ℓ)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-setoid)
open import Data.Container.FreeMonad using (impure)
open import Container.Interpret.Plain using (Congruent)
open import Algebra.Bundles using (Monoid)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl; cong; cong₂; sym; trans)
import Relation.Binary.PropositionalEquality.Properties as ≡P

open import Slides.Scene.Syntax
open import Slides.Scene.Events {T} {D} M Sb
open import Slides.Scene.Arith M Sb
open import Slides.Scene.Sample {T} {D} {X} M Sb val O
import Slides.Scene.Laws M Sb val O as L
open import Slides.Scene.Duration M Sb val O using (gap; duration-par-gap; par-gap)
import Slides.Scene.Algebra
open OrdMon M
open Overlays O using (_⊙_)

-- Readings up to pointwise equality; meanings are a duration and a reading

TimedS : Setoid 0ℓ 0ℓ
TimedS = ×-setoid (≡P.setoid T) (Monoid.setoid RdMonoid)

module TS = Setoid TimedS

_≈ᵗ_ : Timed → Timed → Set
_≈ᵗ_ = TS._≈_

mk≈ : ∀ {x y : Timed} → proj₁ x ≡ proj₁ y → (∀ t q → proj₂ x t q ≡ proj₂ y t q) → x ≈ᵗ y
mk≈ d r = d , r

-- the signature is congruent for it
open Slides.Scene.Algebra.Congruence M (Monoid.setoid RdMonoid) rdP

congRd : IsCongruent
congRd = record
  { par-cong = λ a b t q → cong₂ merge (a t q) (b t q)
  ; clip-cong = λ w a t q → cong (win w t) (a t q)
  ; shift-cong = λ w a t q → back-cong w t (λ u → a u q)
  ; drive-cong = λ c a t q → a t (just c) }

dirCong≈ : Congruent (SceneC T D) TimedS dirH
dirCong≈ = handler-congruent congRd

-- Two scenes are equal when, whatever the leaves read, their durations and readings are

infix 4 _≈ₛ_
_≈ₛ_ : ∀ {A : Set} → Scene T D A → Scene T D A → Set
_≈ₛ_ {A} a b = ∀ (ℓ : A → T → X) → sample ℓ a TS.≈ sample ℓ b

sceneSetoid : Set → Setoid 0ℓ 0ℓ
sceneSetoid A = record
  { Carrier = Scene T D A ; _≈_ = _≈ₛ_
  ; isEquivalence = record { refl = λ _ → TS.refl ; sym = λ e ℓ → TS.sym (e ℓ) ; trans = λ e f ℓ → TS.trans (e ℓ) (f ℓ) } }

-- every operation respects it
impure-cong : ∀ {A : Set} o {k k′ : arity o → Scene T D A} → (∀ q → k q ≈ₛ k′ q) → impure (o , k) ≈ₛ impure (o , k′)
impure-cong o e ℓ = dirCong≈ o (λ q → e q ℓ)

-- equal meanings (events) are equal scenes
media-≈ : ∀ {A : Set} (a b : Scene T D A) → mediaOf a ≡ mediaOf b → a ≈ₛ b
media-≈ a b e ℓ =
  trans (sym (proj₁ (events-sample ℓ a))) (trans (cong proj₁ e) (proj₁ (events-sample ℓ b))) ,
  λ t q → trans (sym (proj₂ (proj₂ (events-sample ℓ a)) t q))
                (trans (cong (λ m → readE ℓ (proj₂ m) t q) e) (proj₂ (proj₂ (events-sample ℓ b)) t q))

-- Hudak's axioms

par-assoc : ∀ {A : Set} (a b c : Scene T D A) → (a ∥ b) ∥ c ≈ₛ a ∥ (b ∥ c)
par-assoc a b c ℓ = mk≈ (⊔-assoc _ _ _) (λ t q → merge-assoc (proj₂ (sample ℓ a) t q) (proj₂ (sample ℓ b) t q) (proj₂ (sample ℓ c) t q))

module _ (⊙-comm : ∀ a b → a ⊙ b ≡ b ⊙ a) where
  par-comm : ∀ {A : Set} (a b : Scene T D A) → a ∥ b ≈ₛ b ∥ a
  par-comm a b ℓ = mk≈ (⊔-comm _ _) (λ t q → L.merge-comm ⊙-comm (proj₂ (sample ℓ a) t q) (proj₂ (sample ℓ b) t q))

-- absence is the unit of `∥`: a gap no longer than the scene
par-unit : ∀ {A : Set} (a s : Scene T D A) {d} → 0# ≤ d → d ≤ duration a → a ∥ gap d s ≈ₛ a
par-unit a s 0≤d d≤a ℓ =
  mk≈ (trans (sym (proj₁ (events-sample ℓ (a ∥ gap _ s)))) (trans (duration-par-gap 0≤d a s d≤a) (proj₁ (events-sample ℓ a))))
      (λ t q → par-gap ℓ a _ s t q)

seq-assoc : ∀ {A : Set} (a b c : Scene T D A) → (a ⨾ b) ⨾ c ≈ₛ a ⨾ (b ⨾ c)
seq-assoc a b c ℓ = L.seq-assoc ℓ a b c

delay-delay : ∀ {A : Set} {δ ε} → 0# ≤ δ → 0# ≤ ε → (s : Scene T D A) → delay δ (delay ε s) ≈ₛ delay (δ + ε) s
delay-delay {δ = δ} {ε} 0≤δ 0≤ε s = media-≈ (delay δ (delay ε s)) (delay (δ + ε) s) (L.delay-delay 0≤δ 0≤ε (mediaOf s))

delay-zero : ∀ {A : Set} (s : Scene T D A) → delay 0# s ≈ₛ s
delay-zero s = media-≈ (delay 0# s) s (L.delay-zero (mediaOf s))

hold-par : ∀ {A : Set} d (a b : Scene T D A) → hold d (a ∥ b) ≈ₛ hold d a ∥ hold d b
hold-par d a b ℓ = mk≈ (sym (⊔-≥ ≤-refl)) (λ t q → win-merge (pos d) t _ _)

delay-par : ∀ {A : Set} d (a b : Scene T D A) → delay d (a ∥ b) ≈ₛ delay d a ∥ delay d b
delay-par d a b ℓ = mk≈ (+-⊔ _ _ _) (λ t q → back-merge (pos d) t (λ u → proj₂ (sample ℓ a) u q) (λ u → proj₂ (sample ℓ b) u q))

drive-par : ∀ {A : Set} c (a b : Scene T D A) → drive c (a ∥ b) ≈ₛ drive c a ∥ drive c b
drive-par c a b ℓ = mk≈ refl (λ t q → refl)

-- a narrow window inside a wide one is the narrow window
hold-hold : ∀ {A : Set} {a b} → a ≤ b → (s : Scene T D A) → hold a (hold b s) ≈ₛ hold a s
hold-hold {a = a} {b} a≤b s ℓ = mk≈ refl (λ t q → go t _)
  where
    pa≤pb : pos a ≤ pos b
    pa≤pb = ⊔-lub (⊔-ub₁ 0# b) (≤-trans a≤b (⊔-ub₂ 0# b))

    go : ∀ t y → win (pos a) t (win (pos b) t y) ≡ win (pos a) t y
    go t y with 0# ≤? t
    ... | no _ = refl
    ... | yes _ with pos a ≤? t
    ...   | yes _ = refl
    ...   | no _ with pos b ≤? t
    go t y | yes _ | no pa≰t | yes pb≤t = ⊥-elim (pa≰t (≤-trans pa≤pb pb≤t))
    go t y | yes _ | no _    | no _     = refl
