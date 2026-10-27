{-# OPTIONS --safe --without-K #-}

-- Laws of the footprint: padding and a pause touch nothing, `Seq` and `Par` take unions, the swap law and exchanging
-- the sides of a `Par` preserve it up to permutation, and independence is symmetric.
module Slides.Anim.Footprint.Properties where

open import Data.List using (List; []; _++_)
import Data.List.Properties as LP
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-trans; ↭-sym; ↭-refl)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PP
open import Data.Bool using (true; false)
open import Data.Unit using (⊤)
open import Data.Nat using (_<ᵇ_)
open import Data.Product using (_,_)
open import Data.String using (String; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; sym)
open import Data.List.Relation.Binary.Disjoint.DecPropositional _≟_ using (Disjoint; disjoint?)
import Data.List.Relation.Binary.Disjoint.Propositional.Properties as DP

open import Slides.Diagram.Scalar using (Ops)
open import Slides.Diagram.Syntax using (fold)
open import Slides.Diagram.Names using (namesAlgebra; Usage)
open import Slides.Diagram.Names.Properties using (names-mapDia)
open import Data.Rational using (ℚ)
open import Slides.Diagram.Expr using (Expr; evalWith)
open import Slides.Diagram.Euclid using (DExpr; evalD; natD)
open import Slides.Diagram.Syntax using (Dia)
open import Slides.Anim.Syntax

open import Slides.Anim.Footprint

-- a template declares the names of every one of its instances
-- (not so for a function body, which may declare different names at different parameters)
bodyUsage-template : ∀ {S} (O : Ops S) (d : Dia (Expr ⊤)) (q q′ : ℚ) →
                     bodyUsage {S} (template d) q ≡ fold namesAlgebra (bodyAt O (template d) q′)
bodyUsage-template O d q q′ = sym (names-mapDia (evalWith O (λ _ → Ops.fromℕ O (units q′))) d)

-- and so does a discrete one
bodyUsage-discrete : ∀ {S} (O : Ops S) (d : Dia (DExpr ⊤)) (q q′ : ℚ) →
                     bodyUsage {S} (discrete d) q ≡ fold namesAlgebra (bodyAt O (discrete d) q′)
bodyUsage-discrete O d q q′ = sym (names-mapDia (λ e → Ops.fromℕ O (evalD natD (λ _ → units q′) e)) d)

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

independent-sym : ∀ {S} {a b : Anim S (Seg S)} → Independent a b → Independent b a
independent-sym = DP.sym
