{-# OPTIONS --safe --without-K #-}

-- Kinds of binding: `on` decodes its keys; `choice` of pairwise disjoint kinds loses none.

module Slides.Backend.Input.Properties where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.AllPairs using (AllPairs; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Nullary.Decidable using (Dec; yes; no; True; toWitness)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; trans; sym)

open import Slides.Input.Binding
open import Slides.Input.Binding.Properties
open import Slides.Backend.Input

module _ {I S : Set} (_≟I_ : DecidableEquality I) where
  open import Data.List.Membership.DecPropositional _≟I_ using (_∈?_)

  on-∈ : ∀ {ks : List I} {i} (s : S) → i ∈ ks → on _≟I_ ks s i ≡ just s
  on-∈ {ks} {i} s m with i ∈? ks
  ... | yes _ = refl
  ... | no ¬m = ⊥-elim (¬m m)

-- Each kind of a disjoint list still decodes its inputs.
choice-∈ : ∀ {I S} {ds : List (Decoder I S)} {d} → AllPairs Disjoint ds → d ∈ ds →
           ∀ i {s} → d i ≡ just s → choice ds i ≡ just s
choice-∈ {ds = d ∷ ds} (_ ∷ _) (here refl) i e = ⊕-left d (choice ds) i e
choice-∈ {ds = d′ ∷ ds} {d} (dis ∷ ap) (there m) i e with All.lookup dis m i
... | inj₁ n rewrite n = choice-∈ ap m i e
... | inj₂ n = ⊥-elim (just≢nothing (trans (sym e) n))
  where just≢nothing : ∀ {A : Set} {x : A} → just x ≡ nothing → _
        just≢nothing ()

-- A statement about every key name, checked by computation over the finite list.
module _ {P : KeyName → Set} (P? : ∀ n → Dec (P n)) where

  ∀-names : True (All.all? P? names) → ∀ n → P n
  ∀-names t n = All.lookup (toWitness t) (names-cover n)

isNothing? : ∀ {A : Set} (m : Maybe A) → Dec (m ≡ nothing)
isNothing? (just _) = no λ ()
isNothing? nothing  = yes refl
