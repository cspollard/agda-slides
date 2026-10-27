{-# OPTIONS --safe --without-K #-}

-- The navigation vocabulary every deck requires (docs/Input.md).
--
-- `next` and `pause` are the commands a program *awaits*; the others are sent by a
-- navigating backend and interpreted by `Slides.Input.Navigation.navM`.  `goto` is by
-- index, `gotoLabel` by the name given by `label` in the program.

module Slides.Input.Nav where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Properties using () renaming (_≟_ to _≟ℕ_)
open import Data.String.Base using (String)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using () renaming (≡-dec to ⊎-dec)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
import Data.String.Properties as Str

open import Slides.DecEq using (retract-dec)

data Nav : Set where
  next prev first last : Nav
  goto      : ℕ → Nav
  gotoLabel : String → Nav

-- Decidable equality as a retract of `ℕ ⊎ ℕ ⊎ String` (`Slides.DecEq`): one clause per
-- constructor, not per pair of constructors.
private
  enc : Nav → ℕ ⊎ (ℕ ⊎ String)
  enc next          = inj₁ 0
  enc prev          = inj₁ 1
  enc first         = inj₁ 2
  enc last          = inj₁ 3
  enc (goto n)      = inj₂ (inj₁ n)
  enc (gotoLabel s) = inj₂ (inj₂ s)

  unenc : ℕ ⊎ (ℕ ⊎ String) → Nav
  unenc (inj₁ 0)        = next
  unenc (inj₁ 1)        = prev
  unenc (inj₁ 2)        = first
  unenc (inj₁ _)        = last
  unenc (inj₂ (inj₁ n)) = goto n
  unenc (inj₂ (inj₂ s)) = gotoLabel s

  unenc-enc : ∀ n → unenc (enc n) ≡ n
  unenc-enc next          = refl
  unenc-enc prev          = refl
  unenc-enc first         = refl
  unenc-enc last          = refl
  unenc-enc (goto _)      = refl
  unenc-enc (gotoLabel _) = refl

_≟N_ : DecidableEquality Nav
_≟N_ = retract-dec enc unenc unenc-enc (⊎-dec _≟ℕ_ (⊎-dec _≟ℕ_ Str._≟_))
