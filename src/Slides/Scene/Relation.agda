{-# OPTIONS --safe --without-K #-}

-- The logical relation of two temporal algebras, once.
--
-- A relation on meanings is a relation `RT` of durations and a relation `RP` of payloads.  If the
-- five operations of the payload preserve it (`Logical`), then so do `holdC`, `delayC`, `parC`,
-- `driveC` and the derived `seqC` and `repC`, so a consumer proves the five and the leaf and gets
-- the handler cases of `pfold-rel` (events against readings: `Slides.Scene.Sample`; two clocks:
-- `Slides.Scene.Tick`).

open import Slides.Scalar.Core using (OrdMon)
import Slides.Scene.Algebra

module Slides.Scene.Relation {T₁ T₂ D₁ D₂ P₁ P₂ : Set} (M₁ : OrdMon T₁) (M₂ : OrdMon T₂)
  (A₁ : Slides.Scene.Algebra.Payload M₁ D₁ P₁) (A₂ : Slides.Scene.Algebra.Payload M₂ D₂ P₂)
  (RT : T₁ → T₂ → Set) (RD : D₁ → D₂ → Set) (RP : P₁ → P₂ → Set) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

private
  module O₁ = OrdMon M₁
  module O₂ = OrdMon M₂
  module X₁ = Slides.Scene.Algebra M₁
  module X₂ = Slides.Scene.Algebra M₂
  module Y₁ = X₁.Temporal A₁
  module Y₂ = X₂.Temporal A₂
  module P₁ = X₁.Payload A₁
  module P₂ = X₂.Payload A₂

record Logical : Set where
  field
    RT-0   : RT O₁.0# O₂.0#
    RT-+   : ∀ {a a′ b b′} → RT a a′ → RT b b′ → RT (a O₁.+ b) (a′ O₂.+ b′)
    RT-⊔   : ∀ {a a′ b b′} → RT a a′ → RT b b′ → RT (a O₁.⊔ b) (a′ O₂.⊔ b′)
    RT-pos : ∀ {w w′} → RT w w′ → RT (X₁.pos w) (X₂.pos w′)
    RP-none  : RP P₁.none P₂.none
    RP-par   : ∀ {p p′ q q′} → RP p q → RP p′ q′ → RP (P₁.par p p′) (P₂.par q q′)
    RP-clip  : ∀ {w w′ p q} → RT w w′ → RP p q → RP (P₁.clip (X₁.pos w) p) (P₂.clip (X₂.pos w′) q)
    RP-shift : ∀ {w w′ p q} → RT w w′ → RP p q → RP (P₁.shift (X₁.pos w) p) (P₂.shift (X₂.pos w′) q)
    RP-drive : ∀ {c c′ p q} → RD c c′ → RP p q → RP (P₁.driveP c p) (P₂.driveP c′ q)

-- meanings are related when their durations and payloads are
R : Y₁.Med → Y₂.Med → Set
R x y = RT (proj₁ x) (proj₁ y) × RP (proj₂ x) (proj₂ y)

module _ (L : Logical) where
  open Logical L

  rel-par : ∀ {x x′ y y′} → R x x′ → R y y′ → R (Y₁.parC x y) (Y₂.parC x′ y′)
  rel-par (d , p) (e , q) = RT-⊔ d e , RP-par p q

  rel-hold : ∀ {w w′ x x′} → RT w w′ → R x x′ → R (Y₁.holdC w x) (Y₂.holdC w′ x′)
  rel-hold w (_ , p) = RT-pos w , RP-clip w p

  rel-delay : ∀ {w w′ x x′} → RT w w′ → R x x′ → R (Y₁.delayC w x) (Y₂.delayC w′ x′)
  rel-delay w (d , p) = RT-+ (RT-pos w) d , RP-shift w p

  rel-drive : ∀ {c c′ x x′} → RD c c′ → R x x′ → R (Y₁.driveC c x) (Y₂.driveC c′ x′)
  rel-drive c (d , p) = d , RP-drive c p

  rel-seq : ∀ {x x′ y y′} → R x x′ → R y y′ → R (Y₁.seqC x y) (Y₂.seqC x′ y′)
  rel-seq rx@(dx , _) ry@(dy , _) =
    RT-+ dx dy , proj₂ (rel-par (rel-hold dx rx) (rel-delay dx (rel-hold dy ry)))

  rel-rep : ∀ n {x x′} → R x x′ → R (Y₁.repC n x) (Y₂.repC n x′)
  rel-rep zero    rx = RT-0 , RP-none
  rel-rep (suc n) rx = rel-seq rx (rel-rep n rx)
