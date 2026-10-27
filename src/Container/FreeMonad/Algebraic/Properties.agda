{-# OPTIONS --safe --without-K #-}

-- The monad of the adjunction `Free ⊣ Forget` is the free monad on trees: the two are isomorphic as monads.
module Container.FreeMonad.Algebraic.Properties where

open import Level using (Level; lift)
open import Data.Product.Base using (_,_)
open import Data.Container.Core using (Container)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl)

open import Categories.Functor using (Functor)
open import Categories.Adjoint.Properties using (adjoint⇒monad)
open import Categories.Monad using (Monad)
open import Categories.Monad.Morphism using (Monad⇒-id)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ᵥ_)
import Categories.NaturalTransformation.Core as NT
open import Categories.NaturalTransformation.Equivalence using (_≃_)

open import Container.Polynomial
open import Container.FreeMonad
open import Container.FreeMonad.Properties

open import Container.FreeMonad.Algebraic

------------------------------------------------------------------------
-- The monad of the adjunction is the free monad

module Agreement {s p} (c ℓ : Level) (C : Container s p) where
  open Alg c ℓ C

  -- The monad induced by `Free ⊣ Forget`.
  AdjMonad : Monad S
  AdjMonad = adjoint⇒monad Free⊣Forget

  -- The monad built directly on trees.
  TreeMonad : Monad S
  TreeMonad = FreeMonad c ℓ C

  -- The fold into a free algebra is `bind`.
  fold-bind : ∀ {X Y : Setoid c′ ℓ′} (f : Func X (Free₀ C Y)) t →
              Eq Y (fold (FreeAlg Y) f t) (t >>= λ x → f ⟨$⟩ x)
  fold-bind {Y = Y} f (pure _)         = refl⋆ Y _
  fold-bind {Y = Y} f (impure (_ , k)) = refl , λ q → fold-bind f (k q)

  -- Both monads have the same underlying functor up to the identity on carriers.
  tree⇒adj : NaturalTransformation (Free {c = c′} {ℓ = ℓ′} C) (Monad.F AdjMonad)
  tree⇒adj = record
    { η           = λ X → record { to = λ t → t ; cong = λ e → e }
    ; commute     = λ {X} {Y} f {t} → sym⋆ Y (fold-bind _ t)
    ; sym-commute = λ {X} {Y} f {t} → fold-bind _ t
    }

  tree⇒adj-monad : Monad⇒-id AdjMonad TreeMonad
  tree⇒adj-monad = record
    { α         = tree⇒adj
    ; unit-comp = λ {U} {x} → refl⋆ {C = C} U (pure x)
    ; mult-comp = λ {U} {t} →
        sym⋆ U (trans⋆ U (fold-bind {X = Free₀ C U} {Y = U}
                            (record { to = λ x → x ; cong = λ e → e })
                            (t >>= λ x → pure {C = C} x))
                         (bind-assoc (Free₀ C U) (Free₀ C U) U t
                                     (λ x → pure x) (λ x → x)))
    }

  adj⇒tree : NaturalTransformation (Monad.F AdjMonad) (Free {c = c′} {ℓ = ℓ′} C)
  adj⇒tree = record
    { η           = λ X → record { to = λ t → t ; cong = λ e → e }
    ; commute     = λ {X} {Y} f {t} → fold-bind _ t
    ; sym-commute = λ {X} {Y} f {t} → sym⋆ Y (fold-bind _ t)
    }

  adj⇒tree-monad : Monad⇒-id TreeMonad AdjMonad
  adj⇒tree-monad = record
    { α         = adj⇒tree
    ; unit-comp = λ {U} {x} → refl⋆ {C = C} U (pure x)
    ; mult-comp = λ {U} {t} →
        trans⋆ U (fold-bind {X = Free₀ C U} {Y = U}
                    (record { to = λ x → x ; cong = λ e → e }) t)
          (sym⋆ U (trans⋆ U
            (bind-cong {C = C} {A = Free₀ C U} {B = U}
               (fold-bind {X = Free₀ C U} {Y = Free₀ C U}
                  (record { to = λ x → pure {C = C} x ; cong = λ e → lift e }) t)
               (λ e → e))
            (bind-assoc (Free₀ C U) (Free₀ C U) U t
                        (λ x → pure {C = C} x) (λ x → x))))
    }

  -- The two monad morphisms are mutually inverse (both are the identity on
  -- carriers), so `Free ⊣ Forget` induces the free monad on trees.
  tree-adj-tree : adj⇒tree ∘ᵥ tree⇒adj ≃ NT.id
  tree-adj-tree {X} = refl⋆ X _

  adj-tree-adj : tree⇒adj ∘ᵥ adj⇒tree ≃ NT.id
  adj-tree-adj {X} = refl⋆ X _
