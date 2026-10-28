{-# OPTIONS --safe --without-K #-}

-- Plain folds: the curried form of a fold, and its laws, stated once.
--
-- A language over a container `C` is usually interpreted by one handler per command,
-- `(a : Shape C) → (Position C a → A) → A`, and a map from leaves.  `pfold` is that fold.
-- When the handler respects pointwise-equal children (`Congruent`) it is an
-- `⟦ C ⟧`-algebra and `pfold` is `Container.FreeMonad.Algebraic.fold` (`pfold-agrees`).  The
-- laws below are the ones every language re-proved for itself:
--
-- * congruence: pointwise-equal leaves, or equal programs, give equal folds;
-- * the bind law: folding a substitution is folding with the substituted programs folded
--   (`pfold-bind`); for a handler into a monoid this is the statement that the fold of a
--   bind is the fold with the continuation folded;
-- * fusion along a container morphism (`pfold-translate`) and along a lowering
--   (`pfold-lower`), with the pulled-back handler written out.
--
-- Equality of programs is `_≈⋆_` (propositional equality of leaves).

module Container.Interpret.Plain where

open import Level using (Level; _⊔_; 0ℓ; lift)
open import Data.Product.Base using (_,_)
open import Data.Container.Core using (Container; Shape; Position; _⇒_; shape; position)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
open import Data.Container.Relation.Binary.Pointwise using () renaming (_,_ to _,ₚ_)
open import Function.Bundles using (Func)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl; cong)
import Relation.Binary.PropositionalEquality.Properties as ≡P

open import Categories.Functor.Algebra using (F-Algebra)

open import Container.FreeMonad.Algebraic using (module Alg)
open import Container.Lowering
open import Container.Lowering.Properties using (_≈⋆_)

private
  variable
    s p x y : Level

module _ (C : Container s p) where

  -- One handler per command, given the results for its positions.
  Handler : ∀ {a} → Set a → Set (s ⊔ p ⊔ a)
  Handler A = (a : Shape C) → (Position C a → A) → A

  pfold : ∀ {a} {A : Set a} {X : Set x} → Handler A → (X → A) → C ⋆ X → A
  pfold h leaf (pure v)         = leaf v
  pfold h leaf (impure (a , k)) = h a (λ q → pfold h leaf (k q))

  -- Handlers that respect pointwise-equal children.
  Congruent : ∀ {a ℓ} (A : Setoid a ℓ) → Handler (Setoid.Carrier A) → Set (s ⊔ p ⊔ a ⊔ ℓ)
  Congruent A h = ∀ a {k k′} → (∀ q → k q ≈ k′ q) → h a k ≈ h a k′
    where open Setoid A using (_≈_)

module _ {C : Container s p} {a ℓ} (A : Setoid a ℓ) where
  private module A = Setoid A

  module _ {h : Handler C A.Carrier} (c : Congruent C A h) where

    -- Folds with pointwise-equal leaves agree.
    pfold-ext : ∀ {X : Set x} {f g : X → A.Carrier} → (∀ v → f v A.≈ g v) → ∀ t →
                pfold C h f t A.≈ pfold C h g t
    pfold-ext e (pure v)         = e v
    pfold-ext e (impure (_ , k)) = c _ (λ q → pfold-ext e (k q))

    -- Folds respect equality of programs.
    pfold-cong : ∀ {X : Set x} {f : X → A.Carrier} {t u : C ⋆ X} → t ≈⋆ u →
                 pfold C h f t A.≈ pfold C h f u
    pfold-cong {t = pure _}         {pure _}           (lift refl) = A.refl
    pfold-cong {t = pure _}         {impure _}         ()
    pfold-cong {t = impure _}       {pure _}           ()
    pfold-cong {t = impure (a , k)} {impure (.a , k′)} (refl , e)     =
      c a (λ q → pfold-cong (e q))

    -- The bind law.
    pfold-bind : ∀ {X : Set x} {Y : Set y} {f : X → A.Carrier} {f′ : Y → A.Carrier}
                 (g : Y → C ⋆ X) → (∀ y → pfold C h f (g y) A.≈ f′ y) →
                 ∀ t → pfold C h f (t >>= g) A.≈ pfold C h f′ t
    pfold-bind g e (pure y)         = e y
    pfold-bind g e (impure (_ , k)) = c _ (λ q → pfold-bind g e (k q))

    -- Fusion along a lowering: lower every command, or fold it with the lowering folded.
    pfold-lower : ∀ {X : Set x} {D : Container s p} (l : Lowering D C) (f : X → A.Carrier) (t : D ⋆ X) →
                  pfold C h f (lower l t)
                    A.≈ pfold D (λ a k → pfold C h k (l a)) f t
    pfold-lower l f (pure _)         = A.refl
    pfold-lower l f (impure (a , k)) =
      pfold-bind (λ q → lower l (k q)) (λ q → pfold-lower l f (k q)) (l a)

    -- Fusion along a container morphism.
    pfold-translate : ∀ {X : Set x} {D : Container s p} (m : D ⇒ C) (f : X → A.Carrier) (t : D ⋆ X) →
                      pfold C h f (translate m t)
                        A.≈ pfold D (λ a k → h (shape m a) (λ q → k (position m q))) f t
    pfold-translate m f (pure _)         = A.refl
    pfold-translate m f (impure (a , k)) =
      c _ (λ q → pfold-translate m f (k (position m q)))

-- A congruent handler is an algebra of the polynomial functor, and `pfold` is its fold.

module _ (C : Container s p) (A : Setoid (s ⊔ p) (s ⊔ p)) where
  private
    module A = Setoid A
    module G = Alg 0ℓ 0ℓ C

  toAlgebra : (h : Handler C A.Carrier) → Congruent C A h → F-Algebra G.F
  toAlgebra h c = record
    { A = A
    ; α = record
        { to   = λ { (a , k) → h a k }
        ; cong = λ { {_ , _} {_ , _} (refl ,ₚ k≈) → c _ k≈ } } }

  module _ (h : Handler C A.Carrier) (c : Congruent C A h) {X : Set (s ⊔ p)}
           (f : X → A.Carrier) where
    leafFunc : Func (≡P.setoid X) A
    leafFunc = record { to = f ; cong = λ e → A.reflexive (cong f e) }

    pfold-agrees : (t : C ⋆ X) → pfold C h f t A.≈ G.fold (toAlgebra h c) leafFunc t
    pfold-agrees (pure _)         = A.refl
    pfold-agrees (impure (a , k)) = c a (λ q → pfold-agrees (k q))
