{-# OPTIONS --safe --without-K #-}

-- Laws of the footprint: the connectives take unions, the swap law and exchanging the sides of a
-- `Par` preserve it up to permutation, and independence is symmetric.  (There is no padding to
-- touch nothing: absence is the unit of `Par`, `Slides.Time.mergeM`.)
module Slides.Anim.Footprint.Properties where

open import Data.List using (List; _++_)
import Data.List.Properties as LP
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-trans; ↭-sym; ↭-reflexive)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PP
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
import Data.List.Relation.Binary.Disjoint.Propositional.Properties as DP

open import Slides.Diagram.Syntax using (fold)
open import Slides.Diagram.Names using (namesAlgebra)
open import Slides.Diagram.Names.Properties using (names-mapDia)
open import Data.Container.FreeMonad using (_>>=_)
open import Slides.Diagram.Ordered using (OExpr; OOps; evalO)
open import Slides.Diagram.Syntax using (Dia; mapDia)
open import Data.Unit using (⊤)
open import Slides.Anim.Syntax
open import Slides.Anim.Footprint

-- a template declares the names of every one of its instances (the leaf of `Slides.Anim.Sample`)
names-inst : ∀ {S} (O : OOps S) (p : S) (d : Tmpl) →
             fold namesAlgebra (mapDia (evalO O (λ _ → p)) d) ≡ fold namesAlgebra d
names-inst O p d = names-mapDia (evalO O (λ _ → p)) d

-- and so does a discrete one (it is a template): those of the diagram it lowers
names-discrete : ∀ (d : Tmpl) → fold namesAlgebra (discrete d) ≡ fold namesAlgebra d
names-discrete d = names-mapDia _ d

footprint-⨾ : ∀ a b → footprint (a ⨾ b) ≡ footprint a ++ footprint b
footprint-⨾ a b = refl

footprint-∥ : ∀ a b → footprint (a ∥ᵃ b) ≡ footprint a ++ footprint b
footprint-∥ a b = refl

-- `Par` has the footprint of the union, whichever side comes first (up to order)
par-comm-footprint : ∀ a b → footprint (a ∥ᵃ b) ↭ footprint (b ∥ᵃ a)
par-comm-footprint a b = PP.++-comm (footprint a) (footprint b)

-- the swap law does not change the footprint, up to permutation
footprint-swap : ∀ a b c d →
                 footprint ((a ⨾ b) ∥ᵃ (c ⨾ d)) ↭ footprint ((a ∥ᵃ c) ⨾ (b ∥ᵃ d))
footprint-swap a b c d = go (footprint a) (footprint b) (footprint c) (footprint d)
  where
    go : (A B C D : List String) → (A ++ B) ++ (C ++ D) ↭ (A ++ C) ++ (B ++ D)
    go A B C D =
      ↭-trans (↭-reflexive (LP.++-assoc A B (C ++ D)))
      (↭-trans (PP.++⁺ˡ A (↭-trans (↭-sym (↭-reflexive (LP.++-assoc B C D)))
                          (↭-trans (PP.++⁺ʳ D (PP.++-comm B C)) (↭-reflexive (LP.++-assoc C B D)))))
               (↭-reflexive (sym (LP.++-assoc A C (B ++ D)))))

independent-sym : ∀ {a b} → Independent a b → Independent b a
independent-sym = DP.sym
