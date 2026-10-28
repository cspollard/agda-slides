{-# OPTIONS --safe --without-K #-}

-- `Slides.Anim.Syntax.foldS` is the generic fold of `Container.FreeMonad.Algebraic`.
--
-- An interpretation of animations is a carrier with an operation for each node of `TimeC` and a map
-- from leaves.  When the operations respect the carrier's equality in each child (`Congruent`; with
-- `_≡_` on `A` this is a function-extensionality statement, which is why the generic theory uses
-- setoids), that is an `⟦ TimeC ⟧`-algebra on a setoid, and `foldS` is its fold (`foldS-agrees`), so
-- the generic theory applies to `dur`, `timeline`, `footprint`, `Slides.Anim.Sample` and the rest:
-- initiality, Lambek's lemma, and the monad structure: `>>=` of animations is the generic bind, whose
-- fusion with `foldS` is `foldS-bind`.

module Slides.Anim.Syntax.Properties.Generic where

open import Level using (0ℓ)
open import Data.Product.Base using (_,_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
open import Data.Container.Relation.Binary.Pointwise using () renaming (_,_ to _,ₚ_)
open import Function.Bundles using (Func)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl; cong)
import Relation.Binary.PropositionalEquality.Properties as ≡P

open import Categories.Functor.Algebra using (F-Algebra)

open import Container.FreeMonad.Algebraic using (module Alg)
open import Slides.Anim.Syntax using (TOp; tarity; TimeC; foldS)

private module G = Alg 0ℓ 0ℓ TimeC

module _ (A : Setoid 0ℓ 0ℓ) where
  private module A = Setoid A

  -- operations that respect the carrier's equality in each child
  Congruent : ((s : TOp) → (tarity s → A.Carrier) → A.Carrier) → Set
  Congruent alg = ∀ s {k k′ : tarity s → A.Carrier} → (∀ p → k p A.≈ k′ p) → alg s k A.≈ alg s k′

  module _ (alg : (s : TOp) → (tarity s → A.Carrier) → A.Carrier) (c : Congruent alg) where
    toAlgebra : F-Algebra G.F
    toAlgebra = record
      { A = A
      ; α = record
          { to   = λ { (s , k) → alg s k }
          ; cong = λ { {_ , _} {_ , _} (refl ,ₚ k≈) → c _ k≈ } } }

    -- with leaves compared by `_≡_`
    module _ {T : Set} (leaf : T → A.Carrier) where
      leafFunc : Func (≡P.setoid T) A
      leafFunc = record { to = leaf ; cong = λ e → A.reflexive (cong leaf e) }

      foldS-agrees : (t : TimeC ⋆ T) → foldS leaf alg t A.≈ G.fold toAlgebra leafFunc t
      foldS-agrees (pure t)         = A.refl
      foldS-agrees (impure (s , k)) = c s (λ p → foldS-agrees (k p))

      -- substituting then folding is folding with the folded substitution
      foldS-bind : ∀ {U : Set} (leaf′ : U → A.Carrier) (m : TimeC ⋆ U) (g : U → TimeC ⋆ T) →
                   (∀ u → foldS leaf alg (g u) A.≈ leaf′ u) →
                   foldS leaf alg (m >>= g) A.≈ foldS leaf′ alg m
      foldS-bind leaf′ (pure u)         g h = h u
      foldS-bind leaf′ (impure (s , k)) g h = c s (λ p → foldS-bind leaf′ (k p) g h)
