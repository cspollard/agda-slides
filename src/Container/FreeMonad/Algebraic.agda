{-# OPTIONS --safe --without-K #-}

-- The algebraic description of the free monad on a container.
--
-- Fix a container `C` and let `F = ⟦ C ⟧` be its polynomial endofunctor on
-- `S = Setoids c′ ℓ′`.  The category `Alg` of `F`-algebras has a forgetful
-- functor `Forget : Alg ⟶ S`.  We show that `(Free₀ C X , impure)` is the
-- free `F`-algebra on `X`, in the sense of `Categories.FreeObjects.Free`,
-- with unit `pure` and universal extension `fold`.  From this agda-categories
-- provides the adjunction `Free ⊣ Forget`.

module Container.FreeMonad.Algebraic where

open import Level using (Level; _⊔_; lift)
open import Data.Product.Base using (_,_)
open import Data.Container.Core using (Container)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Data.Container.Relation.Binary.Pointwise
  using () renaming (_,_ to _,ₚ_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl)

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Construction.F-Algebras using (F-Algebras)
open import Categories.Functor using (Functor; Endofunctor)
open import Categories.Functor.Algebra
  using (F-Algebra; F-Algebra-Morphism)
open import Categories.FreeObjects.Free using (FreeObject; FO⇒Functor; FO⇒LAdj)
open import Categories.NaturalTransformation using (NaturalTransformation)

open import Container.Polynomial
open import Container.FreeMonad

module Alg {s p} (c ℓ : Level) (C : Container s p) where

  -- All setoids live at levels that absorb those of the container.
  c′ ℓ′ : Level
  c′ = c ⊔ s ⊔ p
  ℓ′ = ℓ ⊔ s ⊔ p

  S = Setoids c′ ℓ′

  -- The polynomial endofunctor of `C`.
  F : Endofunctor S
  F = Poly C

  Alg = F-Algebras F

  -- The forgetful functor from `F`-algebras to setoids.
  Forget : Functor Alg S
  Forget = record
    { F₀           = F-Algebra.A
    ; F₁           = F-Algebra-Morphism.f
    ; identity     = λ {A} → Setoid.refl (F-Algebra.A A)
    ; homomorphism = λ {_} {_} {Z} → Setoid.refl (F-Algebra.A Z)
    ; F-resp-≈     = λ f≈g → f≈g
    }

  -- `Free₀ C X` is an `F`-algebra, via the constructor `impure`.
  FreeAlg : Setoid c′ ℓ′ → F-Algebra F
  FreeAlg X = record
    { A = Free₀ C X
    ; α = record
        { to   = impure
        ; cong = λ { {_ , _} {_ , _} (refl ,ₚ f) → refl , f }
        }
    }

  ----------------------------------------------------------------------
  -- Universal property

  module _ (A : F-Algebra F) {X : Setoid c′ ℓ′} (f : Func X (F-Algebra.A A)) where
    private
      module A = F-Algebra A
      module AA = Setoid A.A
      module X = Setoid X

    fold : C ⋆ X.Carrier → AA.Carrier
    fold (pure x)          = f ⟨$⟩ x
    fold (impure (s₁ , k)) = A.α ⟨$⟩ (s₁ , λ q → fold (k q))

    fold-cong : ∀ {t u} → Eq X t u → fold t AA.≈ fold u
    fold-cong {pure _}         {pure _}         (lift e)    = Func.cong f e
    fold-cong {pure _}         {impure _}       ()
    fold-cong {impure _}       {pure _}         ()
    fold-cong {impure (_ , _)} {impure (_ , _)} (refl , e)  =
      Func.cong A.α (refl ,ₚ λ q → fold-cong (e q))

    -- The unique algebra homomorphism extending `f`.
    fold-morphism : F-Algebra-Morphism (FreeAlg X) A
    fold-morphism = record
      { f        = record { to = fold ; cong = fold-cong }
      ; commutes = AA.refl
      }

    -- Any algebra homomorphism out of the free algebra that restricts to
    -- `f` along `pure` is `fold`.
    fold-unique : (g : F-Algebra-Morphism (FreeAlg X) A) →
                  (∀ {x} → F-Algebra-Morphism.f g ⟨$⟩ pure x AA.≈ f ⟨$⟩ x) →
                  ∀ {t} → F-Algebra-Morphism.f g ⟨$⟩ t AA.≈ fold t
    fold-unique g h {pure _}         = h
    fold-unique g h {impure (_ , k)} =
      AA.trans (F-Algebra-Morphism.commutes g)
               (Func.cong A.α (refl ,ₚ λ q → fold-unique g h {k q}))

  -- `Free₀ C X` is a free object on `X` for `Forget`.
  FreeObj : (X : Setoid c′ ℓ′) → FreeObject Forget X
  FreeObj X = record
    { FX      = FreeAlg X
    ; η       = record { to = pure ; cong = lift }
    ; _*      = λ {A} f → fold-morphism A f
    ; *-lift  = λ {A} f → Setoid.refl (F-Algebra.A A)
    ; *-uniq  = λ {A} f g h → fold-unique A f g h
    }

  -- The free functor and the adjunction `Free ⊣ Forget`.
  FreeFunctor : Functor S Alg
  FreeFunctor = FO⇒Functor Forget FreeObj

  Free⊣Forget = FO⇒LAdj Forget FreeObj
