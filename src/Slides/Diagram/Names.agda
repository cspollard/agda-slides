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
open import Data.Fin using (zero; suc)
open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_; _++_; filterᵇ)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.String using (String; _≟_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Slides.Diagram.Syntax
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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

  usageAlgebra : ∀ {S} → Algebra S Usage
  usageAlgebra (Beside _)             k = both (k zero) (k (suc zero))
  usageAlgebra (Above _)              k = both (k zero) (k (suc zero))
  usageAlgebra Atop                   k = both (k zero) (k (suc zero))
  usageAlgebra LabelAbove             k = both (k zero) (k (suc zero))
  usageAlgebra LabelBelow             k = both (k (suc zero)) (k zero)
  usageAlgebra (Place _ _ _ _)        k = k tt
  usageAlgebra (Overlay _ _)          k = both (k zero) (k (suc zero))
  usageAlgebra (Named n)              k with k tt
  ... | (d , u) = n ∷ d , u
  usageAlgebra (Connect a _ b _ _)    k with k tt
  ... | (d , u) = d , u ++ filterᵇ (λ r → not (member r d)) (a ∷ b ∷ [])
  usageAlgebra _                      _ = nothingUsed

namesAlgebra : ∀ {S} → Algebra S Usage
namesAlgebra = usageAlgebra

-- names a `connect` mentions that its own diagram does not declare
dangling : ∀ {S} → Dia S → List String
dangling d = proj₂ (fold namesAlgebra d)

-- the names a diagram uses do not depend on its sizes: changing the scalar leaves them alone
names-mapDia : ∀ {S T} (f : S → T) (d : Dia S) → fold namesAlgebra (mapDia f d) ≡ fold namesAlgebra d
names-mapDia f (pure ())
names-mapDia f (impure (Rectangle _ _ _ , k))  = refl
names-mapDia f (impure (Disc _ _ , k))         = refl
names-mapDia f (impure (Segment _ _ _ , k))    = refl
names-mapDia f (impure (Text _ _ _ _ , k))     = refl
names-mapDia f (impure (Spacer _ _ , k))       = refl
names-mapDia f (impure (Beside _ , k))
  rewrite names-mapDia f (k zero) | names-mapDia f (k (suc zero)) = refl
names-mapDia f (impure (Above _ , k))
  rewrite names-mapDia f (k zero) | names-mapDia f (k (suc zero)) = refl
names-mapDia f (impure (Atop , k))
  rewrite names-mapDia f (k zero) | names-mapDia f (k (suc zero)) = refl
names-mapDia f (impure (LabelAbove , k))
  rewrite names-mapDia f (k zero) | names-mapDia f (k (suc zero)) = refl
names-mapDia f (impure (LabelBelow , k))
  rewrite names-mapDia f (k zero) | names-mapDia f (k (suc zero)) = refl
names-mapDia f (impure (Overlay _ _ , k))
  rewrite names-mapDia f (k zero) | names-mapDia f (k (suc zero)) = refl
names-mapDia f (impure (Place _ _ _ _ , k))
  rewrite names-mapDia f (k tt) = refl
names-mapDia f (impure (Named n , k))
  rewrite names-mapDia f (k tt) = refl
names-mapDia f (impure (Connect a _ b _ _ , k))
  rewrite names-mapDia f (k tt) = refl
