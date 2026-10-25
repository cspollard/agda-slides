{-# OPTIONS --safe --without-K #-}

-- A second algebra for diagrams: which names are declared and which are
-- connected.  `dangling d` lists the names that a `connect` refers to but no
-- `named` declares; those connections draw nothing, so a deck can assert
-- `dangling d ≡ []` (by `refl`) and have a misspelled name fail to typecheck.

module Slides.Diagram.Names where

open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_; filterᵇ)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _≟_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Slides.Diagram.Syntax

-- names declared, names referred to
Usage : Set
Usage = List String × List String

private
  both : Usage → Usage → Usage
  both (d , r) (d′ , r′) = d ++ d′ , r ++ r′

  nothingUsed : Usage
  nothingUsed = [] , []

  usageConnective : (c : Connective) → (Fin (arity c) → Usage) → Usage
  usageConnective (Beside _ _)     k = both (k zero) (k (suc zero))
  usageConnective (Above _ _)      k = both (k zero) (k (suc zero))
  usageConnective Atop             k = both (k zero) (k (suc zero))
  usageConnective (Margin _ _ _ _) k = k zero
  usageConnective (MinWidth _)     k = k zero
  usageConnective (TopAlign _)     k = k zero
  usageConnective (LabelAbove _)   k = both (k zero) (k (suc zero))
  usageConnective (LabelBelow _)   k = both (k zero) (k (suc zero))

  usageAnnotation : Annotation → Usage → Usage
  usageAnnotation (Named n)             u = both (n ∷ [] , []) u
  usageAnnotation (Connect a _ b _ _)   u = both ([] , a ∷ b ∷ []) u

  member : String → List String → Bool
  member x []       = false
  member x (y ∷ ys) = if ⌊ x ≟ y ⌋ then true else member x ys

namesAlgebra : Algebra Usage
namesAlgebra = record
  { prim       = λ _ → nothingUsed
  ; connective = usageConnective
  ; annotation = usageAnnotation }

-- names a `connect` mentions that nothing declares
dangling : Dia → List String
dangling d with fold namesAlgebra d
... | declared , referred = filterᵇ (λ r → not (member r declared)) referred
