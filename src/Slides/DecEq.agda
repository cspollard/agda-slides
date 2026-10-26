{-# OPTIONS --safe --without-K #-}

-- Decidable equality of data with many constructors, once.
--
-- The formulas the backend ships (`Slides.Anim.Formula.Formula`) and the elements of a diagram
-- (`Slides.Diagram.Element`, whose `group` nests elements) are trees: a label (the constructor
-- and its plain arguments) and a list of subtrees.  Written constructor by constructor, a
-- decidable equality needs a clause for every *pair* of constructors, almost all of them
-- "different constructors, so unequal" (quadratic in the number of constructors).  Instead each
-- type is a *retract* of the rose tree over its labels (`to` and `from` with `from (to x) ≡ x`,
-- one clause per constructor), the rose tree has one decidable equality (`roseEq?`, given one
-- for the labels), and a retract inherits decidable equality (`retract-dec`): if `to x ≡ to y`
-- then `x ≡ from (to x) ≡ from (to y) ≡ y`.  Non-recursive types are retracts of sums and
-- products of types with decidable equality (`Data.Sum.Properties.≡-dec`,
-- `Data.Product.Properties.≡-dec`), which are decidable by construction.

module Slides.DecEq where

open import Data.List using (List; []; _∷_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (map′)

data Rose (A : Set) : Set where
  node : A → List (Rose A) → Rose A

module _ {A : Set} (_≟_ : DecidableEquality A) where
  mutual
    roseEq? : DecidableEquality (Rose A)
    roseEq? (node a as) (node b bs) with a ≟ b | roses? as bs
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ { refl → ¬p refl }
    ... | _        | no ¬p    = no λ { refl → ¬p refl }

    roses? : DecidableEquality (List (Rose A))
    roses? []       []       = yes refl
    roses? []       (_ ∷ _)  = no λ ()
    roses? (_ ∷ _)  []       = no λ ()
    roses? (x ∷ xs) (y ∷ ys) with roseEq? x y | roses? xs ys
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ { refl → ¬p refl }
    ... | _        | no ¬p    = no λ { refl → ¬p refl }

retract-dec : ∀ {X Y : Set} (to : X → Y) (from : Y → X) → (∀ x → from (to x) ≡ x) →
              DecidableEquality Y → DecidableEquality X
retract-dec to from rt _≟_ x y = map′ back (cong to) (to x ≟ to y)
  where back : to x ≡ to y → x ≡ y
        back p = trans (sym (rt x)) (trans (cong from p) (rt y))
