{-# OPTIONS --safe --without-K #-}

-- `Slides.Anim.Syntax.foldA` is the generic fold of `Container.FreeMonad.Algebraic`.
--
-- An interpretation of animations is a carrier with a sequential and a parallel
-- operation, `sq` and `pr`, and a map from leaves.  When the operations respect
-- the carrier's equality, that is an `⟦ AnimC ⟧`-algebra on a setoid, and
-- `foldA` is its fold (`foldA-agrees`), so the generic theory applies to `dur`,
-- `timeline`, `footprint` and the rest: initiality, Lambek's lemma, and the
-- monad structure (`>>=` of animations is the generic bind, whose fusion with
-- `foldA` is `foldA-bind`, proved in `Slides.Anim.Syntax`).

module Slides.Anim.Syntax.Properties.Generic where

open import Level using (0ℓ)
open import Data.Fin using (zero; suc)
open import Data.Product.Base using (_,_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Data.Container.Relation.Binary.Pointwise using () renaming (_,_ to _,ₚ_)
open import Function.Bundles using (Func)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl; cong)
import Relation.Binary.PropositionalEquality.Properties as ≡P

open import Categories.Functor.Algebra using (F-Algebra)

open import Container.FreeMonad.Algebraic using (module Alg)
open import Slides.Anim.Syntax using (Seq; Par; AnimC; foldA)

private module G = Alg 0ℓ 0ℓ AnimC

module _ (A : Setoid 0ℓ 0ℓ) where
  private module A = Setoid A

  -- operations that respect the carrier's equality
  record Congruentᵃ (sq pr : A.Carrier → A.Carrier → A.Carrier) : Set where
    field
      sq-cong : ∀ {a a′ b b′} → a A.≈ a′ → b A.≈ b′ → sq a b A.≈ sq a′ b′
      pr-cong : ∀ {a a′ b b′} → a A.≈ a′ → b A.≈ b′ → pr a b A.≈ pr a′ b′

  module _ (sq pr : A.Carrier → A.Carrier → A.Carrier) (c : Congruentᵃ sq pr) where
    open Congruentᵃ c

    toAlgebra : F-Algebra G.F
    toAlgebra = record
      { A = A
      ; α = record
          { to   = λ { (Seq , k) → sq (k zero) (k (suc zero)) ; (Par , k) → pr (k zero) (k (suc zero)) }
          ; cong = λ { {Seq , _} {Seq , _} (refl ,ₚ k≈) → sq-cong (k≈ zero) (k≈ (suc zero))
                     ; {Par , _} {Par , _} (refl ,ₚ k≈) → pr-cong (k≈ zero) (k≈ (suc zero)) } } }

    -- with leaves compared by `_≡_`
    module _ {T : Set} (leaf : T → A.Carrier) where
      leafFunc : Func (≡P.setoid T) A
      leafFunc = record { to = leaf ; cong = λ e → A.reflexive (cong leaf e) }

      foldA-agrees : (t : AnimC ⋆ T) → foldA leaf sq pr t A.≈ G.fold toAlgebra leafFunc t
      foldA-agrees (pure t)              = A.refl
      foldA-agrees (impure (Seq , k))    = sq-cong (foldA-agrees (k zero)) (foldA-agrees (k (suc zero)))
      foldA-agrees (impure (Par , k))    = pr-cong (foldA-agrees (k zero)) (foldA-agrees (k (suc zero)))
