{-# OPTIONS --safe --without-K #-}

-- THEORY MODULE.  Clocks compose by substitution (docs/Stage4.md).
--
-- A deck of slides is a scene whose leaves are scenes (`Scene (Scene A)`); its flat reading is
-- `join d = d >>= id`.  The reading of `Slides.Anim.Sample` is `foldS` of the algebra `timeAlg`, so
-- reading a substituted scene is reading with the substituted leaf semantics (`foldS-bind`), once the
-- algebra respects equality of timed values in each child (`timeAlg-congruent`: for every clock and
-- every connective, no law of the clock is used).  Equality of timed values is the equal duration and
-- the equal behaviour at every time (no function extensionality).
--
--   nested-flat    foldS ℓ (t >>= f) ≈ foldS (foldS ℓ ∘ f) t

module Slides.Anim.Sample.Properties.Nested where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ)
open import Data.Unit using (tt)
open import Data.Container.FreeMonad using (_>>=_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Slides.Time
import Slides.Anim.Track as Tr
open import Slides.Anim.Syntax
open import Slides.Anim.Sample
open import Slides.Anim.Syntax.Properties.Generic using (Congruent; foldS-bind)

module _ (K : Clock) where
  open Clock K

  -- equal timed values: the same duration, the same behaviour at every time
  TMS : Set → Setoid 0ℓ 0ℓ
  TMS X = record
    { Carrier = TM K X
    ; _≈_ = λ x y → proj₁ x ≡ proj₁ y × ∀ τ → proj₂ x τ ≡ proj₂ y τ
    ; isEquivalence = record
        { refl  = refl , λ _ → refl
        ; sym   = λ { (d , p) → sym d , λ τ → sym (p τ) }
        ; trans = λ { (d , p) (e , q) → trans d e , λ τ → trans (p τ) (q τ) } } }

  private
    ite : ∀ {X : Set} (b : Bool) {u u′ v v′ : Maybe X} → u ≡ u′ → v ≡ v′ → (if b then u else v) ≡ (if b then u′ else v′)
    ite true  p q = p
    ite false p q = q

    module _ {X : Set} where
      open Setoid (TMS X) using (_≈_)

      holdT-cong : ∀ n {x y : TM K X} → x ≈ y → holdT K n x ≈ holdT K n y
      holdT-cong n {_ , f} {_ , g} (_ , p) = refl , λ τ → ite (win K n τ) (p τ) refl

      seqW-cong : ∀ {x x′ y y′ : TM K X} → x ≈ x′ → y ≈ y′ → seqW K x y ≈ seqW K x′ y′
      seqW-cong {n , f} {.n , f′} {m , g} {.m , g′} (refl , p) (refl , q) =
        refl , λ τ → ite (win K (n ℕ.+ m) τ) (ite (τ <ᵇ ι n) (p τ) (q (τ - ι n))) refl

      delayT-cong : ∀ n {x y : TM K X} → x ≈ y → delayT K n x ≈ delayT K n y
      delayT-cong n {m , f} {.m , g} (refl , p) = refl , λ τ → ite (τ <ᵇ ι n) refl (p (τ - ι n))

      loopT-cong : ∀ n {x y : TM K X} → x ≈ y → loopT K n x ≈ loopT K n y
      loopT-cong ℕ.zero    h = refl , λ _ → refl
      loopT-cong (ℕ.suc n) h = seqW-cong h (loopT-cong n h)

  -- the algebra of `Slides.Anim.Sample` respects equality of timed values in each child
  timeAlg-congruent : ∀ {X : Set} (⊙ : X → X → X) bnd val → Congruent (TMS X) (timeAlg K ⊙ bnd val)
  timeAlg-congruent ⊙ bnd val Seq        h = seqW-cong (h zero) (h (suc zero))
  timeAlg-congruent ⊙ bnd val Par {k} {k′} h with k zero | k′ zero | k (suc zero) | k′ (suc zero) | h zero | h (suc zero)
  ... | n , f | .n , f′ | m , g | .m , g′ | refl , p | refl , q =
    refl , λ τ → cong₂ (mergeM ⊙) (p τ) (q τ)
  timeAlg-congruent ⊙ bnd val (Hold n)   h = holdT-cong n (h tt)
  timeAlg-congruent ⊙ bnd val (Delay n)  h = delayT-cong n (h tt)
  timeAlg-congruent ⊙ bnd val (Repeat n) h = loopT-cong n (h tt)
  timeAlg-congruent ⊙ bnd val (Drive tr) {k} {k′} h with k tt | k′ tt | h tt
  ... | n , f | .n , f′ | refl , p = refl , λ τ → cong (Maybe.map (bnd (val tr τ))) (p τ)

  -- SUBSTITUTION: reading a bound scene is reading with the leaf semantics substituted
  nested-flat : ∀ {A B X : Set} ⊙ bnd val (ℓ : B → TM K X) (t : Scene A) (f : A → Scene B) →
    let open Setoid (TMS X) using (_≈_) in
    foldS ℓ (timeAlg K ⊙ bnd val) (t >>= f) ≈ foldS (λ a → foldS ℓ (timeAlg K ⊙ bnd val) (f a)) (timeAlg K ⊙ bnd val) t
  nested-flat ⊙ bnd val ℓ t f = foldS-bind (TMS _) (timeAlg K ⊙ bnd val) (timeAlg-congruent ⊙ bnd val) ℓ _ t f (λ _ → Setoid.refl (TMS _))
