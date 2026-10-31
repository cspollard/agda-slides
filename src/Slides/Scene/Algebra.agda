{-# OPTIONS --safe --without-K #-}

-- The temporal algebra, once: the meaning of a scene is a duration and a payload (events, or a
-- reading), and the payload needs only five operations.
--
--   Payload   none, par, clip (the window [0, w)), shift, driveP
--   Temporal  from a payload the duration-carrying `parC holdC delayC driveC`, the derived
--             `seqC` ("`a` held for its duration beside `b` delayed by it") and `repC`, and the
--             handler of the scene signature, congruent at `_≡_`
--
-- Events (`Slides.Scene.Events`) and readings (`Slides.Scene.Sample`) are two payloads; the
-- relation preserved by the five operations is preserved by `seqC`, `repC` and the fold
-- (`Slides.Scene.Relation`).  Durations below zero read as zero (`pos`).

open import Slides.Scalar.Core using (OrdMon)

module Slides.Scene.Algebra {T : Set} (M : OrdMon T) where

open import Data.Fin using (zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
import Relation.Binary.PropositionalEquality.Properties as ≡P

open import Container.Interpret.Plain using (Handler; Congruent)
open import Slides.Scene.Syntax
open OrdMon M

pos : T → T
pos d = 0# ⊔ d

pos-nonneg : ∀ d → 0# ≤ pos d
pos-nonneg d = ⊔-ub₁ 0# d

pos-≤ : ∀ {d} → 0# ≤ d → pos d ≡ d
pos-≤ 0≤d = ⊔-≤ 0≤d

record Payload (D P : Set) : Set where
  field
    none         : P
    par          : P → P → P
    clip shift   : T → P → P
    driveP       : D → P → P

module Temporal {D P : Set} (A : Payload D P) where
  open Payload A

  Med : Set
  Med = T × P

  parC : Med → Med → Med
  parC (d , p) (e , q) = d ⊔ e , par p q

  holdC delayC : T → Med → Med
  holdC w (_ , p)  = pos w , clip (pos w) p
  delayC w (d , p) = pos w + d , shift (pos w) p

  driveC : D → Med → Med
  driveC c (d , p) = d , driveP c p

  seqC : Med → Med → Med
  seqC x y = proj₁ x + proj₁ y , proj₂ (parC (holdC (proj₁ x) x) (delayC (proj₁ x) (holdC (proj₁ y) y)))

  repC : ℕ → Med → Med
  repC zero    x = 0# , none
  repC (suc n) x = seqC x (repC n x)

  handler : Handler (SceneC T D) Med
  handler Seq        k = seqC (k zero) (k (suc zero))
  handler Par        k = parC (k zero) (k (suc zero))
  handler (Hold d)   k = holdC d (k tt)
  handler (Delay d)  k = delayC d (k tt)
  handler (Repeat n) k = repC n (k tt)
  handler (Drive c)  k = driveC c (k tt)

  -- at `_≡_` every handler is congruent
  handler-≡ : Congruent (SceneC T D) (≡P.setoid Med) handler
  handler-≡ Seq        e = cong₂ seqC (e zero) (e (suc zero))
  handler-≡ Par        e = cong₂ parC (e zero) (e (suc zero))
  handler-≡ (Hold d)   e = cong (holdC d) (e tt)
  handler-≡ (Delay d)  e = cong (delayC d) (e tt)
  handler-≡ (Repeat n) e = cong (repC n) (e tt)
  handler-≡ (Drive c)  e = cong (driveC c) (e tt)
