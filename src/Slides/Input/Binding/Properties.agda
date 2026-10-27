{-# OPTIONS --safe --without-K #-}

-- `_⊕_` loses nothing when the kinds are disjoint: each kind still decodes its inputs.

module Slides.Input.Binding.Properties where

open import Data.Empty using (⊥-elim)
open import Data.Maybe.Base using (just; nothing)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; trans; sym)

open import Slides.Input.Binding

⊕-left : ∀ {I S} (r r′ : Decoder I S) i {s} → r i ≡ just s → (r ⊕ r′) i ≡ just s
⊕-left r r′ i e rewrite e = refl

⊕-right : ∀ {I S} (r r′ : Decoder I S) → Disjoint r r′ → ∀ i {s} → r′ i ≡ just s → (r ⊕ r′) i ≡ just s
⊕-right r r′ D i {s} e with D i
... | inj₂ n = ⊥-elim (just≢nothing (trans (sym e) n))
  where just≢nothing : ∀ {A : Set} {x : A} → just x ≡ nothing → _
        just≢nothing ()
... | inj₁ n rewrite n = e
