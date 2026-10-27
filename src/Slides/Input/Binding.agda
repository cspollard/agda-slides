{-# OPTIONS --safe --without-K #-}

-- Binding commands to physical inputs, and the conflict check (docs/Input.md).
--
-- A backend reads a physical input `i : I` (a key, a hash, a button) as a command with a
-- *decoder* `I → Maybe S`.  A finite table `S → I` cannot express families (`goto n`,
-- `gotoLabel s`, reveal's `#/n`), so binding is by command *kind*: `on ks s` is the kind
-- "the inputs `ks` mean `s`", and `choice` combines kinds by `_⊕_` (first match wins).  A
-- conflict is an input two kinds both decode; `Disjoint` rules it out, decidably when the
-- inputs are a known finite list (`disjoint?`; `disjoint*?` for a list of kinds).
-- Laws: `Slides.Input.Binding.Properties`.

module Slides.Input.Binding where

open import Data.Bool.Base using (if_then_else_)
open import Data.List.Base using (List; foldr)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.AllPairs using (AllPairs; allPairs?)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
open import Data.Sum.Base using (_⊎_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (_⊎-dec_; ⌊_⌋)
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

disjoint*? : ∀ {I S} (xs : List I) → (∀ i → i ∈ xs) → (ds : List (Decoder I S)) →
             Dec (AllPairs Disjoint ds)
disjoint*? xs cov = allPairs? (λ r r′ → disjoint? r r′ xs cov)

-- One kind: the inputs `ks` mean the command `s`.
module _ {I S : Set} (_≟I_ : DecidableEquality I) where
  open import Data.List.Membership.DecPropositional _≟I_ using (_∈?_)

  on : List I → S → Decoder I S
  on ks s i = if ⌊ i ∈? ks ⌋ then just s else nothing

choice : ∀ {I S} → List (Decoder I S) → Decoder I S
choice = foldr _⊕_ (λ _ → nothing)
