{-# OPTIONS --safe --without-K #-}

-- Binding by kinds loses nothing when the kinds are disjoint.
--
--   on-∈       a kind decodes its inputs
--   choice-∈   each kind of a pairwise `Disjoint` list still decodes its inputs in the `choice`
--   bind-kind  the same for a list that the instance-checked `bindKeys`/`bindNames` accepted
--              (`True (disjoint*? ...)`)

module Slides.Input.Binding.Properties where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.AllPairs using (AllPairs; _∷_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Nullary.Decidable using (yes; no; True; toWitness)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; trans; sym)

open import Slides.Input.Binding

module _ {I S : Set} (_≟I_ : DecidableEquality I) where
  open import Data.List.Membership.DecPropositional _≟I_ using (_∈?_)

  on-∈ : ∀ {ks : List I} {i} (s : S) → i ∈ ks → on _≟I_ ks s i ≡ just s
  on-∈ {ks} {i} s m with i ∈? ks
  ... | yes _ = refl
  ... | no ¬m = ⊥-elim (¬m m)

choice-∈ : ∀ {I S} {ds : List (Decoder I S)} {d} → AllPairs Disjoint ds → d ∈ ds →
           ∀ i {s} → d i ≡ just s → choice ds i ≡ just s
choice-∈ {ds = d ∷ ds} (_ ∷ _) (here refl) i e rewrite e = refl
choice-∈ {ds = d′ ∷ ds} {d} (dis ∷ ap) (there m) i e with All.lookup dis m i
... | inj₁ n rewrite n = choice-∈ ap m i e
... | inj₂ n = ⊥-elim (just≢nothing (trans (sym e) n))
  where just≢nothing : ∀ {A : Set} {x : A} → just x ≡ nothing → _
        just≢nothing ()

bind-kind : ∀ {I S} (xs : List I) (cov : ∀ i → i ∈ xs) (ds : List (Decoder I S)) →
            True (disjoint*? xs cov ds) → ∀ {d i s} → d ∈ ds → d i ≡ just s → choice ds i ≡ just s
bind-kind xs cov ds ok m e = choice-∈ (toWitness ok) m _ e
