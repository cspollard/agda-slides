{-# OPTIONS --safe --without-K #-}

-- THEORY MODULE.  Laws of the reading `Slides.Anim.Sample`, for any clock: the duration of the
-- reading is `dur`, the window and the tick clock (`win-ι`: whole ticks are in the window exactly
-- when the naturals are), and a segment shows its template at the track's value in its window.
module Slides.Anim.Sample.Properties where

open import Data.Bool using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Container.FreeMonad using (pure; impure)
open import Data.Fin using (zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Slides.Diagram.Syntax using (mapDia)
open import Slides.Diagram.Ordered using (evalO)
open import Slides.Time
import Slides.Anim.Track as Tr
open import Slides.Anim.Syntax
open import Slides.Anim.Sample

module _ (K : Clock) where
  open Clock K

  private
    loop-dur : ∀ {X} n (x : TM K X) → proj₁ (loopT K n x) ≡ n ℕ.* proj₁ x
    loop-dur ℕ.zero    x = refl
    loop-dur (ℕ.suc n) x = cong (proj₁ x ℕ.+_) (loop-dur n x)

  -- the duration of any reading of a scene is `dur`
  sample-dur : ∀ {A X} ⊙ bnd val (ℓ : A → X) (a : Scene A) → proj₁ (sample K ⊙ bnd val ℓ a) ≡ dur a
  sample-dur ⊙ bnd val ℓ (pure a)             = refl
  sample-dur ⊙ bnd val ℓ (impure (Seq , k))   = cong₂ ℕ._+_ (sample-dur ⊙ bnd val ℓ (k zero)) (sample-dur ⊙ bnd val ℓ (k (suc zero)))
  sample-dur ⊙ bnd val ℓ (impure (Par , k))   = cong₂ ℕ._⊔_ (sample-dur ⊙ bnd val ℓ (k zero)) (sample-dur ⊙ bnd val ℓ (k (suc zero)))
  sample-dur ⊙ bnd val ℓ (impure (Hold n , k))   = refl
  sample-dur ⊙ bnd val ℓ (impure (Delay n , k))  = cong (n ℕ.+_) (sample-dur ⊙ bnd val ℓ (k tt))
  sample-dur ⊙ bnd val ℓ (impure (Repeat n , k)) =
    trans (loop-dur n (sample K ⊙ bnd val ℓ (k tt))) (cong (n ℕ.*_) (sample-dur ⊙ bnd val ℓ (k tt)))
  sample-dur ⊙ bnd val ℓ (impure (Drive tr , k)) = sample-dur ⊙ bnd val ℓ (k tt)

  frames-dur : ∀ val (a : Anim) → proj₁ (frames K val a) ≡ dur a
  frames-dur val a = sample-dur _ _ val _ a

  -- a segment shows its template at the track's value, in its window
  frames-seg : ∀ val tr d τ →
    proj₂ (frames K val (seg tr d)) τ
    ≡ (if win K (Tr.dur tr) τ then just (inst K (val tr τ) d) else nothing)
  frames-seg val tr d τ with win K (Tr.dur tr) τ
  ... | true  = refl
  ... | false = refl

module _ (K : Clock) (L : ClockLaws K) where
  open Clock K
  open ClockLaws L

  -- whole ticks are in the window exactly when the naturals are
  win-ι : ∀ n k → win K n (ι k) ≡ (k ℕ.<ᵇ n)
  win-ι n k rewrite sym ι-0 | ι-<ᵇ k 0 | ι-<ᵇ k n = refl
