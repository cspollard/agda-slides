{-# OPTIONS --safe --without-K #-}

-- Laws of the animation syntax: the durations of the connectives and of the derived forms.
-- (`foldS` commutes with `>>=` in `Slides.Anim.Syntax.Properties.Generic`; `par` no longer pads, so
-- there is no padding law: a gap is `Delay k (Hold 0 _)` and absence is the unit of `Par`.)
module Slides.Anim.Syntax.Properties where

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; _+_; _⊔_)
import Data.Nat.Properties as ℕP
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import Slides.Diagram.Syntax using (Dia)
import Slides.Anim.Track as T
open import Slides.Anim.Syntax

dur-⨾ : ∀ {A} (a b : Scene A) → dur (a ⨾ b) ≡ dur a + dur b
dur-⨾ a b = refl

dur-∥ : ∀ {A} (a b : Scene A) → dur (a ∥ᵃ b) ≡ dur a ⊔ dur b
dur-∥ a b = refl

-- a segment lasts as long as its track
dur-seg : ∀ tr d → dur (seg tr d) ≡ T.dur tr
dur-seg tr d = refl

dur-gap : ∀ n → dur (gap n) ≡ n
dur-gap n = ℕP.+-identityʳ n

-- a flipbook shows one frame per tick
dur-flipbook : ∀ (fs : List (Dia ℕ)) → dur (flipbook fs) ≡ length fs
dur-flipbook []       = refl
dur-flipbook (f ∷ fs) = cong (1 +_) (dur-flipbook fs)
