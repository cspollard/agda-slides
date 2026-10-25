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
-- permutation of its draws and anchors) is `Slides.Diagram.Commute`.

module Slides.Anim.Footprint where

open import Data.List using (List; []; _∷_; _++_)
import Data.List.Properties as LP
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-refl; ↭-trans; ↭-sym)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PP
open import Data.Bool using (true; false)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (_<ᵇ_)
open import Data.Product using (_,_; proj₁)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (True)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)
open import Data.List.Relation.Binary.Disjoint.DecPropositional _≟_ using (Disjoint; disjoint?)
import Data.List.Relation.Binary.Disjoint.Propositional.Properties as DP

open import Slides.Diagram.Scalar using (Ops)
open import Slides.Diagram.Syntax using (fold)
open import Slides.Diagram.Names using (namesAlgebra)
import Slides.Anim.Track as T
open import Slides.Anim.Syntax

-- the names a segment's frame declares
footprint : ∀ {S} → Anim S (Seg S) → List String
footprint = foldA (λ s → proj₁ (fold namesAlgebra (body s (T.start (track s))))) _++_ _++_

footprint-⨾ : ∀ {S} (a b : Anim S (Seg S)) → footprint (a ⨾ b) ≡ footprint a ++ footprint b
footprint-⨾ a b = refl

footprint-∥ : ∀ {S} (a b : Anim S (Seg S)) → footprint (a ∥ᵃ b) ≡ footprint a ++ footprint b
footprint-∥ a b = refl

-- a pause touches nothing, so padding leaves the footprint alone
footprint-none : ∀ {S} (O : Ops S) n → footprint (none O n) ≡ []
footprint-none O n = refl

footprint-pad : ∀ {S} (O : Ops S) n (a : Anim S (Seg S)) → footprint (pad O n a) ≡ footprint a
footprint-pad O n a with dur a <ᵇ n
... | true  = LP.++-identityʳ (footprint a)
... | false = refl

-- `par` has the footprint of the union, whichever side comes first (up to order)
footprint-par : ∀ {S} (O : Ops S) (a b : Anim S (Seg S)) →
                footprint (par O a b) ≡ footprint a ++ footprint b
footprint-par O a b = cong₂ _++_ (footprint-pad O (dur b) a) (footprint-pad O (dur a) b)

par-comm-footprint : ∀ {S} (O : Ops S) (a b : Anim S (Seg S)) →
                     footprint (par O a b) ↭ footprint (par O b a)
par-comm-footprint O a b rewrite footprint-par O a b | footprint-par O b a = PP.++-comm (footprint a) (footprint b)

-- the swap law does not change the footprint, up to permutation
footprint-swap : ∀ {S} (a b c d : Anim S (Seg S)) →
                 footprint ((a ⨾ b) ∥ᵃ (c ⨾ d)) ↭ footprint ((a ∥ᵃ c) ⨾ (b ∥ᵃ d))
footprint-swap a b c d = go (footprint a) (footprint b) (footprint c) (footprint d)
  where
    open import Relation.Binary.PropositionalEquality using (sym; subst)
    open import Data.List.Relation.Binary.Permutation.Propositional using (↭-reflexive)
    go : (A B C D : List String) → (A ++ B) ++ (C ++ D) ↭ (A ++ C) ++ (B ++ D)
    go A B C D =
      ↭-trans (↭-reflexive (LP.++-assoc A B (C ++ D)))
      (↭-trans (PP.++⁺ˡ A (↭-trans (↭-sym (↭-reflexive (LP.++-assoc B C D)))
                          (↭-trans (PP.++⁺ʳ D (PP.++-comm B C)) (↭-reflexive (LP.++-assoc C B D)))))
               (↭-reflexive (sym (LP.++-assoc A C (B ++ D)))))

-- independent animations: no name in common (decidable; symmetric)
Independent : ∀ {S} → Anim S (Seg S) → Anim S (Seg S) → Set
Independent a b = Disjoint (footprint a) (footprint b)

independent? : ∀ {S} (a b : Anim S (Seg S)) → Dec (Independent a b)
independent? a b = disjoint? (footprint a) (footprint b)

independent-sym : ∀ {S} {a b : Anim S (Seg S)} → Independent a b → Independent b a
independent-sym = DP.sym

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
