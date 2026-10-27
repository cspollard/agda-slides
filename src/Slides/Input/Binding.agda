{-# OPTIONS --safe --without-K #-}

-- Binding commands to physical inputs, and the conflict check (docs/Input.md).
--
-- A backend reads a physical input `i : I` (a key, a hash, a button) as a command with a
-- *decoder* `I → Maybe S`.  A finite table `S → I` cannot express families (`goto n`,
-- `gotoLabel s`, reveal's `#/n`), so binding is by command *kind*: one decoder per kind,
-- combined by `_⊕_` (first match wins).  A conflict is an input two kinds both decode;
-- `Disjoint` rules it out, decidably when the inputs are a known finite list
-- (`disjoint?`).  The finite-table special case is `conflict?`: `S → I` injective.
-- Laws: `Slides.Input.Binding.Properties`.

module Slides.Input.Binding where

open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (all?) renaming (_≟_ to _≟F_)
open import Data.List.Base using (List)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties using ()
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (_→-dec_; _⊎-dec_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

Decoder : Set → Set → Set
Decoder I S = I → Maybe S

infixr 5 _⊕_
_⊕_ : ∀ {I S} → Decoder I S → Decoder I S → Decoder I S
(r ⊕ r′) i = maybe′ just (r′ i) (r i)

-- No input is decoded by both kinds.
Disjoint : ∀ {I S} → Decoder I S → Decoder I S → Set
Disjoint r r′ = ∀ i → r i ≡ nothing ⊎ r′ i ≡ nothing

private
  nothing? : ∀ {A : Set} (m : Maybe A) → Dec (m ≡ nothing)
  nothing? (just _) = no λ ()
  nothing? nothing  = yes refl

-- Decidable over a finite list of all inputs.
disjoint? : ∀ {I S} (r r′ : Decoder I S) (xs : List I) → (∀ i → i ∈ xs) → Dec (Disjoint r r′)
disjoint? r r′ xs cover with All.all? (λ i → nothing? (r i) ⊎-dec nothing? (r′ i)) xs
... | yes a = yes λ i → All.lookup a (cover i)
... | no ¬a = no λ D → ¬a (All.tabulate λ {i} _ → D i)

-- A finite table from `n` commands to inputs is conflict-free iff it is injective.
conflict? : ∀ {n} {I : Set} → DecidableEquality I → (t : Fin n → I) →
            Dec (∀ i j → t i ≡ t j → i ≡ j)
conflict? _≟_ t = all? λ i → all? λ j → (t i ≟ t j) →-dec (i ≟F j)
