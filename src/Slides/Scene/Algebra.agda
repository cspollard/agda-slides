{-# OPTIONS --safe --without-K #-}

-- The temporal algebra, once: the meaning of a scene is a duration and a payload (events, or a
-- reading), and the payload needs only five operations.
--
--   Payload   none, par, clip (the window [0, w)), shift, driveP
--   Temporal  from a payload the duration-carrying `parC holdC delayC driveC`, the derived
--             `seqC` ("`a` held for its duration beside `b` delayed by it") and `repC`, and the
--             handler of the scene signature, congruent at `_≡_` and, when the five operations are, at
--             any setoid of payloads (`Congruence`)
--
-- Events (`Slides.Scene.Events`) and readings (`Slides.Scene.Sample`) are two payloads; the
-- relation preserved by the five operations is preserved by `seqC`, `repC` and the fold
-- (`Slides.Scene.Relation`).  Durations below zero read as zero (`pos`).

open import Slides.Scalar.Core using (OrdMon)

module Slides.Scene.Algebra {T : Set} (M : OrdMon T) where

open import Level using (0ℓ)
open import Data.Fin using (zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-setoid)
open import Data.Unit using (tt)
open import Relation.Binary.Bundles using (Setoid)
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

-- congruence at a setoid of payloads
module Congruence {D : Set} (S : Setoid 0ℓ 0ℓ) (A : Payload D (Setoid.Carrier S)) where
  open Setoid S using (_≈_) renaming (refl to ≈-refl)
  open Payload A
  open Temporal A

  record IsCongruent : Set where
    field
      par-cong   : ∀ {p p′ q q′} → p ≈ p′ → q ≈ q′ → par p q ≈ par p′ q′
      clip-cong  : ∀ w {p p′} → p ≈ p′ → clip w p ≈ clip w p′
      shift-cong : ∀ w {p p′} → p ≈ p′ → shift w p ≈ shift w p′
      drive-cong : ∀ c {p p′} → p ≈ p′ → driveP c p ≈ driveP c p′

  module _ (C : IsCongruent) where
    open IsCongruent C
    private module MS = Setoid (×-setoid (≡P.setoid T) S)

    infix 4 _≈ᴹ_
    _≈ᴹ_ = MS._≈_

    par≈ : ∀ {x x′ y y′} → x ≈ᴹ x′ → y ≈ᴹ y′ → parC x y ≈ᴹ parC x′ y′
    par≈ {_ , _} {_ , _} {_ , _} {_ , _} (refl , a) (refl , b) = refl , par-cong a b

    hold≈ : ∀ w {x x′} → x ≈ᴹ x′ → holdC w x ≈ᴹ holdC w x′
    hold≈ w {_ , _} {_ , _} (_ , a) = refl , clip-cong _ a

    delay≈ : ∀ w {x x′} → x ≈ᴹ x′ → delayC w x ≈ᴹ delayC w x′
    delay≈ w {_ , _} {_ , _} (refl , a) = refl , shift-cong _ a

    seq≈ : ∀ {x x′ y y′} → x ≈ᴹ x′ → y ≈ᴹ y′ → seqC x y ≈ᴹ seqC x′ y′
    seq≈ {_ , _} {_ , _} {_ , _} {_ , _} (refl , a) (refl , b) = refl , par-cong (clip-cong _ a) (shift-cong _ (clip-cong _ b))

    rep≈ : ∀ n {x x′} → x ≈ᴹ x′ → repC n x ≈ᴹ repC n x′
    rep≈ zero    e = refl , ≈-refl
    rep≈ (suc n) e = seq≈ e (rep≈ n e)

    handler-congruent : Congruent (SceneC T D) (×-setoid (≡P.setoid T) S) handler
    handler-congruent Seq        e = seq≈ (e zero) (e (suc zero))
    handler-congruent Par        e = par≈ (e zero) (e (suc zero))
    handler-congruent (Hold d)   e = hold≈ d (e tt)
    handler-congruent (Delay d)  e = delay≈ d (e tt)
    handler-congruent (Repeat n) e = rep≈ n (e tt)
    handler-congruent (Drive c)  e = (proj₁ (e tt)) , drive-cong c (proj₂ (e tt))
