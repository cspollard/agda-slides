{-# OPTIONS --safe --without-K #-}

-- Durations, absence and the boundary of `Seq`, on readings.
--
--   win-zero, absent-sample   `hold 0# s` shows nothing
--   gap-sample                a gap `delay d (hold 0# s)` shows nothing for `d`
--   par-gap, duration-par-gap a gap is the unit of `Par` on readings, and on durations when no
--                             longer than the scene
--   seq-before, seq-after, seq-boundary
--                             `a ⨾ b` shows `a` before its duration and `b` from its own time 0
--                             after it: right-continuity
--   duration-nonneg           every scene has a non-negative duration (the boundary laws need it)
--
-- Duration clauses: sum for `⨾`, the window for `hold`, delay plus scene for `delay`, `n` times for
-- `repeat`.  `events-sample` (`Slides.Scene.Sample`) carries these to events.

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Slides.Scalar.Core using (OrdMon; Sub)
open import Slides.Diagram.Overlay using (Overlays)

module Slides.Scene.Duration {T D X : Set} (M : OrdMon T) (Sb : Sub M) (val : D → T → T) (O : Overlays X) where

open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (refl; cong; cong₂; sym; trans)

open import Slides.Scene.Syntax
open import Slides.Scene.Events {T} {D} M Sb
open import Slides.Scene.Arith M Sb
open import Slides.Scene.Sample {T} {D} {X} M Sb val O
open import Slides.Scene.Laws M Sb val O using (duration-nonneg)
open OrdMon M
open Sub Sb

-- Durations (the events' fold; the clauses are the handler's)

module _ {A : Set} where

  duration-seq : ∀ (a b : Scene T D A) → duration (a ⨾ b) ≡ duration a + duration b
  duration-seq a b = refl

  duration-hold : ∀ d (a : Scene T D A) → duration (hold d a) ≡ pos d
  duration-hold d a = refl

  duration-delay : ∀ d (a : Scene T D A) → duration (delay d a) ≡ pos d + duration a
  duration-delay d a = refl

  duration-drive : ∀ c (a : Scene T D A) → duration (drive c a) ≡ duration a
  duration-drive c a = refl

  -- n copies take n times as long
  infixr 7 _·_
  _·_ : ℕ → T → T
  zero  · d = 0#
  suc n · d = d + n · d

  duration-repeat : ∀ n (a : Scene T D A) → duration (repeat n a) ≡ n · duration a
  duration-repeat zero    a = refl
  duration-repeat (suc n) a = cong (duration a +_) (duration-repeat n a)

  -- a window of a non-negative length is that long
  duration-hold-≤ : ∀ {d} → 0# ≤ d → ∀ (a : Scene T D A) → duration (hold d a) ≡ d
  duration-hold-≤ 0≤d a = pos-≤ 0≤d

-- absence: a scene held for nothing
absent : ∀ {A : Set} → Scene T D A → Scene T D A
absent s = hold 0# s

-- a gap of length `d`: a scene shown for nothing, after `d`
gap : ∀ {A : Set} → T → Scene T D A → Scene T D A
gap d s = delay d (absent s)

duration-gap : ∀ {A : Set} {d} → 0# ≤ d → (s : Scene T D A) → duration (gap d s) ≡ d
duration-gap {d = d} 0≤d s rewrite pos-≤ (≤-refl {0#}) | pos-≤ 0≤d = +-idʳ d

-- Windows and shifts of readings

win-zero : ∀ t (y : Maybe X) → win 0# t y ≡ nothing
win-zero t y with 0# ≤? t
... | no _  = refl
... | yes h with 0# ≤? t
...   | yes _ = refl
...   | no ¬h = ⊥-elim (¬h h)

win-in : ∀ {w t} → 0# ≤ t → ¬ (w ≤ t) → ∀ y → win w t y ≡ y
win-in {w} {t} 0≤t w≰t y with 0# ≤? t
... | no ¬h = ⊥-elim (¬h 0≤t)
... | yes _ with w ≤? t
...   | yes h = ⊥-elim (w≰t h)
...   | no _  = refl

win-out : ∀ {w t} → w ≤ t → ∀ y → win w t y ≡ nothing
win-out {w} {t} w≤t y with 0# ≤? t
... | no _ = refl
... | yes _ with w ≤? t
...   | yes _ = refl
...   | no ¬h = ⊥-elim (¬h w≤t)

back-before : ∀ {w t} → ¬ (w ≤ t) → ∀ r → back w t r ≡ nothing
back-before {w} {t} w≰t r with w ≤? t
... | yes h = ⊥-elim (w≰t h)
... | no _  = refl

back-after : ∀ {w t} → w ≤ t → ∀ r → back w t r ≡ r (t - w)
back-after {w} {t} w≤t r with w ≤? t
... | yes _ = refl
... | no ¬h = ⊥-elim (¬h w≤t)

-- Absence and gaps

absent-sample : ∀ {A : Set} (ℓ : A → T → X) (s : Scene T D A) t q →
                proj₂ (sample ℓ (absent s)) t q ≡ nothing
absent-sample ℓ s t q rewrite pos-≤ (≤-refl {0#}) = win-zero t _

-- a gap is absent: before its start by `back`, after it by absence
gap-sample : ∀ {A : Set} (ℓ : A → T → X) d (s : Scene T D A) t q →
             proj₂ (sample ℓ (gap d s)) t q ≡ nothing
gap-sample ℓ d s t q with pos d ≤? t
... | no _  = refl
... | yes _ = absent-sample ℓ s _ q

-- absence is the unit of `Par`, on readings
par-gap : ∀ {A : Set} (ℓ : A → T → X) (a : Scene T D A) d (s : Scene T D A) t q →
          proj₂ (sample ℓ (a ∥ gap d s)) t q ≡ proj₂ (sample ℓ a) t q
par-gap ℓ a d s t q = trans (cong (merge (proj₂ (sample ℓ a) t q)) (gap-sample ℓ d s t q))
                            (merge-nothing _)

-- ... and on durations, when the gap is no longer than the scene
duration-par-gap : ∀ {A : Set} {d} → 0# ≤ d → (a : Scene T D A) (s : Scene T D A) →
                   d ≤ duration a → duration (a ∥ gap d s) ≡ duration a
duration-par-gap 0≤d a s d≤a = trans (cong (duration a ⊔_) (duration-gap 0≤d s)) (⊔-≥ d≤a)

-- The boundary of Seq

module _ {A : Set} (ℓ : A → T → X) (a b : Scene T D A) where
  private
    da = proj₁ (sample ℓ a)
    db = proj₁ (sample ℓ b)
    nn = duration-nonneg (leafT ℓ) (λ _ → ≤-refl)

  -- before the first operand's duration, only the first is seen
  seq-before : ∀ {t} q → 0# ≤ t → ¬ (da ≤ t) → proj₂ (sample ℓ (a ⨾ b)) t q ≡ proj₂ (sample ℓ a) t q
  seq-before {t} q 0≤t da≰t rewrite pos-≤ (nn a) | pos-≤ (nn b) =
    trans (cong₂ merge (win-in 0≤t da≰t (proj₂ (sample ℓ a) t q)) (back-before da≰t (λ u → win db u (proj₂ (sample ℓ b) u q)))) (merge-nothing _)

  -- from its duration on, the second is seen at its own local time, inside its own window
  seq-after : ∀ {t} q → da ≤ t →
              proj₂ (sample ℓ (a ⨾ b)) t q ≡ win db (t - da) (proj₂ (sample ℓ b) (t - da) q)
  seq-after {t} q da≤t rewrite pos-≤ (nn a) | pos-≤ (nn b) =
    cong₂ merge (win-out da≤t (proj₂ (sample ℓ a) t q)) (back-after da≤t (λ u → win db u (proj₂ (sample ℓ b) u q)))

  -- right-continuity: at the boundary itself the second operand is at its time 0
  seq-boundary : ∀ q → ¬ (db ≤ 0#) → proj₂ (sample ℓ (a ⨾ b)) da q ≡ proj₂ (sample ℓ b) 0# q
  seq-boundary q db≰0 rewrite seq-after q (≤-refl {da}) | sub-self da = win-in ≤-refl db≰0 _
