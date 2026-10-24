{-# OPTIONS --safe --without-K #-}

-- Restyling is a homomorphism of backends.
--
-- Given a function `f` on XML documents that respects `_≈ₓ_` (add a class,
-- wrap in a `div`, …), `map f` is an algebra homomorphism from the content
-- algebra of `Slides.Backend.Reveal` to the algebra that applies `f` to the
-- markup of every command.  `Container.Interpret.fold-hom` then says that
-- mapping `f` over a rendered program equals interpreting it with the
-- restyled algebra, so restyling can be done by post-processing.

module Slides.Backend.Restyle where

open import Level using (0ℓ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl)
import Data.List.Relation.Binary.Pointwise as PW

open import Data.Container.Relation.Binary.Pointwise
  using () renaming (_,_ to _,ₚ_)
open import Categories.Functor.Algebra using (F-Algebra; F-Algebra-Morphism)

open import Data.Container.FreeMonad using (_⋆_)
open import Data.XML.AST using (XMLDoc)
open import Data.XML.Equality using (_≈ₓ_; XMLSetoid)

open import Container.Polynomial using (Poly₀; Poly₁)
open import Container.Interpret using (module Fusion)
open import Slides.Core
open import Slides.Backend.Common

module _ (f : XMLDoc → XMLDoc) (f-cong : ∀ {x y} → x ≈ₓ y → f x ≈ₓ f y) where

  -- `map f` on forests.
  mapForest : Func ForestSetoid ForestSetoid
  mapForest = record
    { to   = map f
    ; cong = λ e → PW.map⁺ f f (PW.map f-cong e)
    }

  -- The content algebra with `f` applied to the markup of each command.
  restyledContentα : Func (Poly₀ ContentC ForestSetoid) ForestSetoid
  restyledContentα = record
    { to   = λ { (c , k) → map f (renderContent c) ++ k tt }
    ; cong = λ { {_ , _} {_ , _} (refl ,ₚ k≈) →
                 PW.++⁺ (Setoid.refl ForestSetoid {map f (renderContent _)}) (k≈ tt) }
    }

  restyledContentAlg : F-Algebra A.F
  restyledContentAlg = record { A = ForestSetoid ; α = restyledContentα }

  -- `map f` is an algebra homomorphism.
  restyle-hom : F-Algebra-Morphism contentAlg restyledContentAlg
  restyle-hom = record
    { f        = mapForest
    ; commutes = λ {x} → commutes x
    }
    where
      commutes : ∀ x → Setoid._≈_ ForestSetoid
        (map f (Func.to (F-Algebra.α contentAlg) x))
        (Func.to restyledContentα (Func.to (Poly₁ ContentC mapForest) x))
      commutes (c , k) rewrite map-++ f (renderContent c) (k tt) =
        Setoid.refl ForestSetoid {map f (renderContent c) ++ map f (k tt)}

  -- Interpreting with the restyled algebra is mapping `f` over the rendering.
  restyle : ∀ (t : Content) →
    Setoid._≈_ ForestSetoid
      (map f (renderContentProgram t))
      (A.fold restyledContentAlg {⊤ˢ}
         (record { to   = λ x → map f (Func.to nil x)
                 ; cong = λ e → Func.cong mapForest (Func.cong nil e) }) t)
  restyle = Fusion.fold-hom 0ℓ 0ℓ ContentC {contentAlg} {restyledContentAlg} {⊤ˢ} restyle-hom nil
