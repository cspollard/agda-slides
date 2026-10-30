{-# OPTIONS --safe --without-K #-}

-- Tick positions: an arithmetic progression, `ap s d n = s, s + d, …` (n terms).
--
--   ap-length   n terms                          ap-sorted   0 ≤ d → the terms are in order
--
-- Equal spacing is the definition (the tail starts at `s + d`).  Which progression an axis gets
-- (a "nice" step, the first multiple in range) is chosen in the model (`Slides.Plot.Ticks.Rat`).

open import Slides.Scalar.Core using (OrdMon)

module Slides.Plot.Ticks {K : Set} (M : OrdMon K) where

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Linked using (Linked; []; [-]; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

open OrdMon M

ap : K → K → ℕ → List K
ap s d zero    = []
ap s d (suc n) = s ∷ ap (s + d) d n

ap-length : ∀ s d n → length (ap s d n) ≡ n
ap-length s d zero    = refl
ap-length s d (suc n) = cong suc (ap-length (s + d) d n)

ap-sorted : ∀ {d} → 0# ≤ d → ∀ s n → Linked _≤_ (ap s d n)
ap-sorted 0≤d s zero          = []
ap-sorted 0≤d s (suc zero)    = [-]
ap-sorted {d} 0≤d s (suc (suc n)) = subst (_≤ s + d) (+-idʳ s) (+-mono ≤-refl 0≤d) ∷ ap-sorted 0≤d (s + d) (suc n)
