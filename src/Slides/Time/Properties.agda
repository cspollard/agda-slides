{-# OPTIONS --safe --without-K #-}

-- THEORY MODULE.  The laws of the temporal skeleton, stated against any `Clock` (so at ℚ they are
-- corollaries): `Par` runs both sides at the same time and takes the longer duration; `Seq` runs
-- the first side up to its duration, then the second from its own time 0 (right-continuity at the
-- boundary).  Only the clock laws are used.  The instances of the laws are at the end.
module Slides.Time.Properties where

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

open import Slides.Time
open import Slides.Time.Rat using (ratClock)
open import Slides.Time.Nat using (natClock)
import Slides.Diagram.Ordered.Properties as OP
import Slides.Diagram.NatQ.Properties as NP

module _ (K : Clock) (L : ClockLaws K) where
  open Clock K
  open ClockLaws L
  open Sem K

  seqAt-before : ∀ {A} (n m : ℕ) (f g : T → A) τ → (τ <ᵇ ι n) ≡ true →
                 proj₂ (seqAt (n , f) (m , g)) τ ≡ f τ
  seqAt-before n m f g τ h rewrite h = refl

  seqAt-after : ∀ {A} (n m : ℕ) (f g : T → A) τ → (τ <ᵇ ι n) ≡ false →
                proj₂ (seqAt (n , f) (m , g)) τ ≡ g (τ - ι n)
  seqAt-after n m f g τ h rewrite h = refl

  private
    lt-irrefl : ∀ n → (n ℕ.<ᵇ n) ≡ false
    lt-irrefl ℕ.zero    = refl
    lt-irrefl (ℕ.suc n) = lt-irrefl n

    ι-self : ∀ n → ι n - ι n ≡ 0#
    ι-self n = trans (sym (ι-∸ n n (≤-refl n))) ι-0′
      where
        ≤-refl : ∀ n → n ℕ.≤ n
        ≤-refl ℕ.zero    = ℕ.z≤n
        ≤-refl (ℕ.suc n) = ℕ.s≤s (≤-refl n)
        ι-0′ : ι (n ℕ.∸ n) ≡ 0#
        ι-0′ = trans (cong ι (n∸n n)) ι-0
          where n∸n : ∀ n → n ℕ.∸ n ≡ 0
                n∸n ℕ.zero    = refl
                n∸n (ℕ.suc n) = n∸n n

  -- at the boundary the second takes over, from its own time 0
  seqAt-boundary : ∀ {A} (n m : ℕ) (f g : T → A) →
                   proj₂ (seqAt (n , f) (m , g)) (ι n) ≡ g 0#
  seqAt-boundary n m f g =
    trans (seqAt-after n m f g (ι n) (trans (ι-<ᵇ n n) (lt-irrefl n))) (cong g (ι-self n))

  parAt-time : ∀ {F} (_⊙_ : F → F → F) (A B : Timed (Maybe F)) τ →
               proj₂ (parAt _⊙_ A B) τ ≡ mergeM _⊙_ (proj₂ A τ) (proj₂ B τ)
  parAt-time _⊙_ A B τ = refl

  parAt-dur : ∀ {F} (_⊙_ : F → F → F) (A B : Timed (Maybe F)) →
              proj₁ (parAt _⊙_ A B) ≡ proj₁ A ℕ.⊔ proj₁ B
  parAt-dur _⊙_ A B = refl

-- overlay commutes with a map that is a homomorphism of the overlay
mergeM-map : ∀ {A B : Set} (f : A → B) (⊙ : A → A → A) (⊙′ : B → B → B) →
             (∀ x y → f (⊙ x y) ≡ ⊙′ (f x) (f y)) → ∀ a b →
             Maybe.map f (mergeM ⊙ a b) ≡ mergeM ⊙′ (Maybe.map f a) (Maybe.map f b)
mergeM-map f ⊙ ⊙′ h nothing  b        = refl
mergeM-map f ⊙ ⊙′ h (just x) nothing  = refl
mergeM-map f ⊙ ⊙′ h (just x) (just y) = cong just (h x y)

------------------------------------------------------------------------
-- The instances

ratLaws : ClockLaws ratClock
ratLaws = record
  { lt-spec = λ _ _ _ _ → refl ; ι-0 = refl ; ι-+ = NP.ι-+ ; ι-<ᵇ = OP.ι-<ᵇ ; ι-∸ = NP.ι-∸ }

natLaws : ClockLaws natClock
natLaws = record
  { lt-spec = λ _ _ _ _ → refl ; ι-0 = refl ; ι-+ = λ _ _ → refl ; ι-<ᵇ = λ _ _ → refl ; ι-∸ = λ _ _ _ → refl }
