{-# OPTIONS --safe --without-K #-}

-- What an animation touches: the names its frames declare.
--
-- `footprint` is `foldA` into lists of names (both connectives take the union,
-- here the concatenation).  Two animations in `Par` are independent when their
-- footprints are disjoint; then no name is shared, so which of two anchors a
-- `connect` finds does not depend on the order in which the frames are overlaid.
--
-- Proved:
--   * `none` touches nothing, so padding does not change the footprint
--   * `Seq` and `Par` take unions, so the footprint is invariant under the swap
--     law and under exchanging the sides of a `Par`, up to permutation (`_↭_`)
--   * disjointness is decidable and symmetric
--
-- Commutativity of `Par` on the frames themselves (`atop` is commutative up to a
-- permutation of its draws and anchors) is `Slides.Diagram.Place.Properties.Commute`.

module Slides.Anim.Footprint where

open import Data.List using (List; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (proj₁)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (True)
open import Data.List.Relation.Binary.Disjoint.DecPropositional _≟_ using (Disjoint; disjoint?)

open import Slides.Diagram.Scalar using (Ops)
open import Slides.Diagram.Syntax using (fold)
open import Slides.Diagram.Names using (namesAlgebra; Usage)
open import Data.Rational using (ℚ)
import Slides.Anim.Track as T
open import Slides.Anim.Syntax

-- the names a segment's frame declares: of a function body, those of its first frame; of a
-- template, those of the template itself (evaluating sizes does not change which names a
-- diagram declares, `names-mapDia`)
bodyUsage : ∀ {S} → SegBody S → ℚ → Usage
bodyUsage (blackBox f) q = fold namesAlgebra (f q)
bodyUsage (template d) q = fold namesAlgebra d
bodyUsage (discrete d) q = fold namesAlgebra d

footprint : ∀ {S} → Anim S (Seg S) → List String
footprint = foldA (λ s → proj₁ (bodyUsage (content s) (T.start (track s)))) _++_ _++_

-- independent animations: no name in common (decidable; symmetric)
Independent : ∀ {S} → Anim S (Seg S) → Anim S (Seg S) → Set
Independent a b = Disjoint (footprint a) (footprint b)

independent? : ∀ {S} (a b : Anim S (Seg S)) → Dec (Independent a b)
independent? a b = disjoint? (footprint a) (footprint b)

-- `par` that only accepts independent operands.  The check is by computation:
-- the instance argument is `⊤` (found as `tt`) when the footprints are disjoint
-- and `⊥` otherwise, so an ill-formed parallel composition fails to typecheck,
-- as a dangling `connect` does.
parI : ∀ {S} (O : Ops S) (a b : Anim S (Seg S)) → {{_ : True (independent? a b)}} → Anim S (Seg S)
parI O a b = par O a b

-- what the instance argument of `parI` is found as (`True` computes to `⊤`)
instance
  ⊤-witness : ⊤
  ⊤-witness = tt
