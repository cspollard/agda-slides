{-# OPTIONS --safe --without-K #-}

-- `⟦C⟧`-algebras are the Eilenberg–Moore algebras of the free monad.
--
-- agda-categories gives the comparison functor
--
--   K : Alg ⟶ EilenbergMoore (monad of Free ⊣ Forget)
--
-- of an adjunction.  Here we build an inverse `Comparison⁻¹` and the two
-- natural isomorphisms, so `Free ⊣ Forget` is a monadic adjunction
-- (`IsMonadicAdjunction`): a backend, an algebra of the signature, is the
-- same thing as an algebra of the free monad.
--
-- All the isomorphisms are the identity on carriers.  The one lemma with
-- content is `fold-action`: for a module `(A , a)`, folding the induced
-- algebra over the identity is `a`.

module Container.FreeMonad.Properties.Monadic where

open import Level using (Level; lift)
open import Data.Product.Base using (_,_)
open import Data.Container.Core using (Container)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Data.Container.Relation.Binary.Pointwise
  using () renaming (_,_ to _,ₚ_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl)

open import Categories.Adjoint.Monadic using (IsMonadicAdjunction)
open import Categories.Adjoint.Properties using ()
open import Categories.Category.Construction.Properties.EilenbergMoore using (ComparisonF)
open import Categories.Category.Equivalence using ()
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Algebra using (F-Algebra)
open import Categories.Monad using (Monad)
open import Categories.NaturalTransformation using ()
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)
import Categories.Category.Construction.EilenbergMoore as EilenbergMooreC

open import Container.Polynomial using ()
open import Container.FreeMonad
open import Container.FreeMonad.Properties
open import Container.FreeMonad.Algebraic
open import Container.FreeMonad.Algebraic.Properties

module Monadic {s p} (c ℓ : Level) (C : Container s p) where
  open Alg c ℓ C
  module Ag = Agreement c ℓ C

  T : Monad S
  T = Ag.AdjMonad

  module EMM = EilenbergMooreC T
  open EMM using (Module; Module⇒; EilenbergMoore)

  ----------------------------------------------------------------------
  -- The inverse of the comparison functor

  -- A module for the free monad gives an algebra for the signature: apply
  -- the action to a node whose children are variables.
  toAlgebra : Module → F-Algebra F
  toAlgebra M = record
    { A = M.A
    ; α = record
        { to   = λ { (s₁ , k) → M.action ⟨$⟩ impure (s₁ , λ q → pure (k q)) }
        ; cong = λ { {_ , _} {_ , _} (refl ,ₚ k≈) →
                     Func.cong M.action (refl , λ q → lift (k≈ q)) }
        }
    }
    where module M = Module M

  Comparison⁻¹ : Functor EilenbergMoore Alg
  Comparison⁻¹ = record
    { F₀           = toAlgebra
    ; F₁           = λ {M} {N} f → record
        { f        = Module⇒.arr f
        ; commutes = λ { {s₁ , k} → Module⇒.commute f {impure (s₁ , λ q → pure (k q))} }
        }
    ; identity     = λ {M} → Setoid.refl (Module.A M)
    ; homomorphism = λ {_} {_} {Z} → Setoid.refl (Module.A Z)
    ; F-resp-≈     = λ eq → eq
    }

  private
    K = ComparisonF Free⊣Forget

    idFunc : (X : Setoid c′ ℓ′) → Func X X
    idFunc X = record { to = λ x → x ; cong = λ e → e }

  ----------------------------------------------------------------------
  -- Algebras → modules → algebras is the identity

  Comparison⁻¹∘K≃id : NaturalIsomorphism (Comparison⁻¹ ∘F K) (idF {C = Alg})
  Comparison⁻¹∘K≃id = record
    { F⇒G = record
        { η           = λ A → record
            { f        = idFunc (F-Algebra.A A)
            ; commutes = Setoid.refl (F-Algebra.A A)
            }
        ; commute     = λ {_} {B} _ → Setoid.refl (F-Algebra.A B)
        ; sym-commute = λ {_} {B} _ → Setoid.refl (F-Algebra.A B)
        }
    ; F⇐G = record
        { η           = λ A → record
            { f        = idFunc (F-Algebra.A A)
            ; commutes = Setoid.refl (F-Algebra.A A)
            }
        ; commute     = λ {_} {B} _ → Setoid.refl (F-Algebra.A B)
        ; sym-commute = λ {_} {B} _ → Setoid.refl (F-Algebra.A B)
        }
    ; iso = λ A → record
        { isoˡ = Setoid.refl (F-Algebra.A A)
        ; isoʳ = Setoid.refl (F-Algebra.A A)
        }
    }

  ----------------------------------------------------------------------
  -- Modules → algebras → modules is the identity

  -- For a module `(A , a)`, folding the induced algebra over the identity
  -- is the action `a`.
  fold-action : ∀ (M : Module) (t : C ⋆ Setoid.Carrier (Module.A M)) →
                Setoid._≈_ (Module.A M)
                  (fold (toAlgebra M) {Module.A M} (idFunc (Module.A M)) t)
                  (Module.action M ⟨$⟩ t)
  fold-action M (pure x)         = Setoid.sym (Module.A M) (Module.identity M)
  fold-action M (impure (s₁ , k)) =
    Setoid.trans (Module.A M)
      (Func.cong (Module.action M) (refl , λ q → lift (fold-action M (k q))))
      (Module.commute M {impure (s₁ , λ q → pure (k q))})

  -- Folding `pure` into the free algebra is the identity on trees.
  fold-pure : ∀ (X : Setoid c′ ℓ′) (t : C ⋆ Setoid.Carrier X) →
              Eq X (fold (FreeAlg X) {X} (record { to = pure ; cong = lift }) t) t
  fold-pure X (pure x)         = lift (Setoid.refl X)
  fold-pure X (impure (_ , k)) = refl , λ q → fold-pure X (k q)

  -- The two directions of the isomorphism at a module `M` differ from the
  -- identity only by `F₁ id`, which `fold-pure` removes.
  to-K∘G : ∀ M → Module⇒ (Functor.F₀ (K ∘F Comparison⁻¹) M) M
  to-K∘G M = record
    { arr     = idFunc (Module.A M)
    ; commute = λ {t} →
        Setoid.trans (Module.A M) (fold-action M t)
          (Func.cong (Module.action M) (sym⋆ (Module.A M) (fold-pure (Module.A M) t)))
    }

  from-K∘G : ∀ M → Module⇒ M (Functor.F₀ (K ∘F Comparison⁻¹) M)
  from-K∘G M = record
    { arr     = idFunc (Module.A M)
    ; commute = λ {t} →
        Setoid.trans (Module.A M)
          (Func.cong (Module.action M) (sym⋆ (Module.A M) (fold-pure (Module.A M) t)))
          (Setoid.sym (Module.A M)
            (fold-action M (fold (FreeAlg (Module.A M)) {Module.A M}
                              (record { to = pure ; cong = lift }) t)))
    }

  K∘Comparison⁻¹≃id : NaturalIsomorphism (K ∘F Comparison⁻¹) (idF {C = EilenbergMoore})
  K∘Comparison⁻¹≃id = record
    { F⇒G = record
        { η           = to-K∘G
        ; commute     = λ {_} {N} _ → Setoid.refl (Module.A N)
        ; sym-commute = λ {_} {N} _ → Setoid.refl (Module.A N)
        }
    ; F⇐G = record
        { η           = from-K∘G
        ; commute     = λ {_} {N} _ → Setoid.refl (Module.A N)
        ; sym-commute = λ {_} {N} _ → Setoid.refl (Module.A N)
        }
    ; iso = λ M → record
        { isoˡ = Setoid.refl (Module.A M)
        ; isoʳ = Setoid.refl (Module.A M)
        }
    }

  ----------------------------------------------------------------------
  -- Free ⊣ Forget is monadic

  Free⊣Forget-monadic : IsMonadicAdjunction Free⊣Forget
  Free⊣Forget-monadic = record
    { Comparison⁻¹   = Comparison⁻¹
    ; comparison-equiv = record
        { F∘G≈id = K∘Comparison⁻¹≃id
        ; G∘F≈id = Comparison⁻¹∘K≃id
        }
    }
