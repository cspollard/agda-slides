{-# OPTIONS --safe --without-K #-}

-- What an animation touches: the names its frames declare.
--
-- `footprint` is `foldS` into lists of names (every connective takes the union, here the
-- concatenation; a leaf declares the names of its template).  Two animations in `Par` are
-- independent when their footprints are disjoint; then no name is shared, so which of two anchors
-- a `connect` finds does not depend on the order in which the frames are overlaid.
--
-- Proved (`Slides.Anim.Footprint.Properties`):
--   * the connectives take unions, so the footprint is invariant under the swap law and under
--     exchanging the sides of a `Par`, up to permutation (`_↭_`)
--   * disjointness is decidable and symmetric
--
-- Commutativity of `Par` on the frames themselves (`atop` is commutative up to a
-- permutation of its draws and anchors) is `Slides.Diagram.Place.Properties.Commute`.

module Slides.Anim.Footprint where

open import Data.List using (List; []; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (proj₁)
open import Data.Fin using (zero; suc)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (True)
open import Data.List.Relation.Binary.Disjoint.DecPropositional _≟_ using (Disjoint; disjoint?)

open import Slides.Diagram.Syntax using (fold)
open import Slides.Diagram.Names using (namesAlgebra)
open import Slides.Anim.Syntax

-- the names a template declares (evaluating its sizes does not change which names a diagram
-- declares, `names-mapDia`)
footprintAlg : (s : TOp) → (tarity s → List String) → List String
footprintAlg Seq        k = k zero ++ k (suc zero)
footprintAlg Par        k = k zero ++ k (suc zero)
footprintAlg (Hold _)   k = k tt
footprintAlg (Delay _)  k = k tt
footprintAlg (Repeat _) k = k tt
footprintAlg (Drive _)  k = k tt

footprint : Anim → List String
footprint = foldS (λ d → proj₁ (fold namesAlgebra d)) footprintAlg

-- independent animations: no name in common (decidable; symmetric)
Independent : Anim → Anim → Set
Independent a b = Disjoint (footprint a) (footprint b)

independent? : (a b : Anim) → Dec (Independent a b)
independent? a b = disjoint? (footprint a) (footprint b)

-- `Par` that only accepts independent operands.  The check is by computation:
-- the instance argument is `⊤` (found as `tt`) when the footprints are disjoint
-- and `⊥` otherwise, so an ill-formed parallel composition fails to typecheck,
-- as a dangling `connect` does.
parI : (a b : Anim) → {{_ : True (independent? a b)}} → Anim
parI a b = a ∥ᵃ b

-- what the instance argument of `parI` is found as (`True` computes to `⊤`)
instance
  ⊤-witness : ⊤
  ⊤-witness = tt
