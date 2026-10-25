{-# OPTIONS --safe --without-K #-}

-- A second algebra for diagrams: which names are declared, and which names a
-- `connect` cannot find.  `dangling d` lists the names that a `connect` refers
-- to but that no `named` inside *that connect's own diagram* declares; such a
-- connection draws nothing, so a deck can assert `dangling d ≡ []` (by `refl`)
-- and have a misspelled name fail to typecheck.  (`Slides.Diagram.NamesSound`
-- proves that this guarantees every connection is drawn.)
--
-- The declared names are listed in the order the layout keeps its anchors.

module Slides.Diagram.Names where

open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_; filterᵇ)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.String using (String; _≟_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Slides.Diagram.Syntax

-- names declared, names a connection could not find
Usage : Set
Usage = List String × List String

member : String → List String → Bool
member x []       = false
member x (y ∷ ys) = if ⌊ x ≟ y ⌋ then true else member x ys

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
  usageConnective (LabelBelow _)   k = both (k (suc zero)) (k zero)

  usageAnnotation : Annotation → Usage → Usage
  usageAnnotation (Named n)             (d , u) = n ∷ d , u
  usageAnnotation (Connect a _ b _ _)   (d , u) = d , u ++ filterᵇ (λ r → not (member r d)) (a ∷ b ∷ [])

namesAlgebra : Algebra Usage
namesAlgebra = record
  { prim       = λ _ → nothingUsed
  ; connective = usageConnective
  ; annotation = usageAnnotation }

-- names a `connect` mentions that its own diagram does not declare
dangling : Dia → List String
dangling d = proj₂ (fold namesAlgebra d)
