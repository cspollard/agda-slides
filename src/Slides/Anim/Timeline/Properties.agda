{-# OPTIONS --safe --without-K #-}

-- Laws of the timeline: its length is the duration of the animation, and the timeline of `Seq` is
-- the concatenation of the timelines (the tick of the second part shifted by the first duration).
-- `Par` is the overlay frame by frame with absence the unit: its laws are those of the clock
-- skeleton (`Slides.Time.Properties`).
module Slides.Anim.Timeline.Properties where

open import Data.Bool using (true; false; if_then_else_)
open import Data.List using (List; _∷_; _++_; length; applyUpTo)
import Data.List.Properties as LP
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
import Data.Maybe as Maybe
open import Data.Nat as ℕ using (ℕ; _+_; _∸_; _<ᵇ_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Slides.Diagram.Syntax using (Dia; spacer)
open import Slides.Time.Nat using (natClock)
open import Slides.Time.Properties using (natLaws)
open import Slides.Anim.Syntax
open import Slides.Anim.Sample
open import Slides.Anim.Sample.Properties
open import Slides.Anim.Timeline
open import Slides.Anim.Arith using (<ᵇ-false)
import Data.Nat.Properties as ℕP

-- the length of the timeline is the duration
length-dur : ∀ a → length (timeline a) ≡ dur a
length-dur a = trans (LP.length-applyUpTo _ _) (frames-dur natClock natVal a)

private
  applyUpTo-++ : ∀ {A : Set} (f : ℕ → A) n m → applyUpTo f (n + m) ≡ applyUpTo f n ++ applyUpTo (λ i → f (n + i)) m
  applyUpTo-++ f ℕ.zero    m = refl
  applyUpTo-++ f (ℕ.suc n) m = cong (f 0 ∷_) (applyUpTo-++ (λ i → f (ℕ.suc i)) n m)

  applyUpTo-ext : ∀ {A : Set} (f g : ℕ → A) n → (∀ k → (k <ᵇ n) ≡ true → f k ≡ g k) → applyUpTo f n ≡ applyUpTo g n
  applyUpTo-ext f g ℕ.zero    h = refl
  applyUpTo-ext f g (ℕ.suc n) h = cong₂ _∷_ (h 0 refl) (applyUpTo-ext (λ i → f (ℕ.suc i)) (λ i → g (ℕ.suc i)) n (λ k hk → h (ℕ.suc k) hk))

  -- the frames of `a ⨾ b` at a tick inside it: the first's, or the second's shifted
  framesN-⨾ : ∀ a b k → (k <ᵇ proj₁ (framesN a) + proj₁ (framesN b)) ≡ true →
              proj₂ (framesN (a ⨾ b)) k
              ≡ (if k <ᵇ proj₁ (framesN a) then proj₂ (framesN a) k else proj₂ (framesN b) (k ∸ proj₁ (framesN a)))
  framesN-⨾ a b k hk rewrite hk with k <ᵇ proj₁ (framesN a)
  ... | true  = refl
  ... | false = refl

-- `Seq` is concatenation of timelines
timeline-⨾ : ∀ a b → timeline (a ⨾ b) ≡ timeline a ++ timeline b
timeline-⨾ a b =
  trans (applyUpTo-ext _ G (n + m) (λ k hk → cong (fromMaybe x₀) (framesN-⨾ a b k hk)))
  (trans (applyUpTo-++ G n m)
         (cong₂ _++_ (applyUpTo-ext G (λ k → fromMaybe x₀ (proj₂ (framesN a) k)) n (λ k hk → cong (λ c → fromMaybe x₀ (if c then proj₂ (framesN a) k else proj₂ (framesN b) (k ∸ n))) hk))
                     (applyUpTo-ext (λ i → G (n + i)) (λ i → fromMaybe x₀ (proj₂ (framesN b) i)) m shift)))
  where
    n = proj₁ (framesN a)
    m = proj₁ (framesN b)
    x₀ : Dia ℕ
    x₀ = spacer 0 0
    G : ℕ → Dia ℕ
    G k = fromMaybe x₀ (if k <ᵇ n then proj₂ (framesN a) k else proj₂ (framesN b) (k ∸ n))
    shift : ∀ i → (i <ᵇ m) ≡ true → G (n + i) ≡ fromMaybe x₀ (proj₂ (framesN b) i)
    shift i _ rewrite <ᵇ-false (ℕP.m≤m+n n i) | ℕP.m+n∸m≡n n i = refl
