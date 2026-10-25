{-# OPTIONS --safe --without-K #-}

-- Looping: the frame shown at time `t` of an animation of `n` frames repeated
-- forever is frame `t mod n` (`Slides.Core.loop`; `animationSync` steps `i ↦ (i + 1)
-- mod n`).  This is the periodic extension of the timeline: it agrees with the
-- timeline on its own `n` ticks, is `n`-periodic, and stepping one tick at a time
-- from the start visits exactly that frame.

module Slides.Anim.Loop where

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; NonZero)
open import Data.Nat.DivMod using (_%_; m%n<n; m<n⇒m%n≡m; [m+n]%n≡m%n; m%n%n≡m%n; %-distribˡ-+)
open import Data.Nat.Properties using (+-comm)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)

-- the frame index shown at tick `t` of a loop of `n` frames
phase : (n : ℕ) → .{{NonZero n}} → ℕ → ℕ
phase n t = t % n

-- it is a valid index
phase< : ∀ n {{_ : NonZero n}} t → phase n t < n
phase< n t = m%n<n t n

-- within the first period the loop is the timeline itself
phase-id : ∀ n {{_ : NonZero n}} t → t < n → phase n t ≡ t
phase-id n t = m<n⇒m%n≡m

-- one period later it is the same frame
phase-period : ∀ n {{_ : NonZero n}} t → phase n (t + n) ≡ phase n t
phase-period n t = [m+n]%n≡m%n t n

-- the player's step `i ↦ (i + 1) mod n` tracks it: after `t` ticks from frame 0 it
-- shows frame `t mod n`
tick : (n : ℕ) → .{{NonZero n}} → ℕ → ℕ
tick n i = (suc i) % n

advance : (n : ℕ) → .{{NonZero n}} → ℕ → ℕ → ℕ
advance n zero    i = i
advance n (suc t) i = tick n (advance n t i)

advance-phase : ∀ n {{_ : NonZero n}} t → advance n t 0 ≡ phase n t
advance-phase (suc k) zero = refl
advance-phase n (suc t) =
  trans (cong (tick n) (advance-phase n t))
    (trans (%-distribˡ-+ 1 (t % n) n)
      (trans (cong (λ x → (1 % n + x) % n) (m%n%n≡m%n t n))
        (sym (%-distribˡ-+ 1 t n))))
