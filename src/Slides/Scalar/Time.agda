{-# OPTIONS --safe --without-K #-}

-- Time: instants and durations.  Sampling depends on this theory (and Coupling) only.
--
-- `Time T` is an ordered monoid with the embedding of whole ticks `tick : ℕ → T` (an order
-- embedding and monoid map) and `floor : T → ℕ`, the right adjoint of `tick` on the
-- non-negative instants: `tick n ≤ x  iff  n ≤ floor x` (`floor-gal`).  From this alone:
-- `floor (tick n) = n`, and `hold x = tick (floor x)` is the sample-and-hold of a tick clock.
-- The remainder `x - hold x` (loops, the phase within a tick) needs exact subtraction, which
-- is the separate optional layer `Sub` of Core (`Rem`).  ℕ and ℚ are models; density and
-- induction are not in the theory and are hypotheses where used.
--
-- Signature: `TimeC` has the one command `Hold`; its ℕ reading is the identity.

module Slides.Scalar.Time where

open import Level using (0ℓ)
open import Data.Nat as ℕ using (ℕ)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Container.Core using (Container; _▷_)
open import Data.Unit using (⊤)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import Relation.Binary.PropositionalEquality.Properties as ≡P

open import Container.Interpret.Plain using (Handler; Congruent)
open import Slides.Scalar.Core

record Time (T : Set) : Set₁ where
  field ord : OrdMon T
  open OrdMon ord public
  field
    tick         : ℕ → T
    floor        : T → ℕ
    tick-0       : tick 0 ≡ 0#
    tick-+       : ∀ m n → tick (m ℕ.+ n) ≡ tick m + tick n
    tick-mono    : ∀ {m n} → m ℕ.≤ n → tick m ≤ tick n
    tick-reflect : ∀ {m n} → tick m ≤ tick n → m ℕ.≤ n
    floor-gal    : ∀ {n x} → 0# ≤ x → (tick n ≤ x → n ℕ.≤ floor x) × (n ℕ.≤ floor x → tick n ≤ x)

  hold : T → T
  hold x = tick (floor x)

  tick-nonneg : ∀ n → 0# ≤ tick n
  tick-nonneg n = subst (_≤ tick n) tick-0 (tick-mono ℕ.z≤n)

  floor-tick : ∀ n → floor (tick n) ≡ n
  floor-tick n = ℕP.≤-antisym
    (tick-reflect (proj₂ (floor-gal (tick-nonneg n)) ℕP.≤-refl))
    (proj₁ (floor-gal (tick-nonneg n)) ≤-refl)

  hold-tick : ∀ n → hold (tick n) ≡ tick n
  hold-tick n = cong tick (floor-tick n)

  hold-≤ : ∀ {x} → 0# ≤ x → hold x ≤ x
  hold-≤ 0≤x = proj₂ (floor-gal 0≤x) ℕP.≤-refl

  -- the part of an instant within its tick: needs exact subtraction
  module Rem (Sb : Sub ord) where
    open Sub Sb

    rem : T → T
    rem x = x - hold x

    rem-split : ∀ {x} → 0# ≤ x → hold x + rem x ≡ x
    rem-split 0≤x = sub-add (hold-≤ 0≤x)

    rem-below : ∀ {x} → 0# ≤ x → ¬ (tick (ℕ.suc (floor x)) ≤ x)
    rem-below 0≤x h = ℕP.1+n≰n (proj₁ (floor-gal 0≤x) h)

    rem-tick : ∀ n → rem (tick n) ≡ 0#
    rem-tick n = trans (cong (λ y → tick n - y) (hold-tick n)) (sub-self (tick n))

------------------------------------------------------------------------
-- The signature

data TimeOp : Set where
  Hold : TimeOp

TimeC : Container 0ℓ 0ℓ
TimeC = TimeOp ▷ λ _ → ⊤

module _ {T} (Tm : Time T) where
  open Time Tm

  timeH : Handler TimeC T
  timeH Hold k = hold (k _)

  timeCong : Congruent TimeC (≡P.setoid T) timeH
  timeCong Hold e = cong hold (e _)
