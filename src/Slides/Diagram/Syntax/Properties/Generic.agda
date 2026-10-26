{-# OPTIONS --safe --without-K #-}

-- `Slides.Diagram.Syntax.fold` is the generic fold of `Container.Interpret`.
--
-- `Syntax.fold` is written out by pattern matching, as a catamorphism over
-- `DiagramC S ⋆ ⊥`.  The generic theory (`Container.FreeMonad.Algebraic`,
-- `Container.Interpret`) works with algebras on setoids, `Func (⟦C⟧ A) A`.  An
-- `Algebra S A` becomes one when its handlers respect pointwise-equal children
-- (`Congruent`; with `_≡_` on `A` this is a function-extensionality
-- statement, which is why the generic theory uses setoids).  Then the two folds
-- agree (`fold-agrees`), so the generic results apply to every renderer:
--
--   * `fold-hom`: a map between carriers that commutes with the handlers
--     commutes with folding (the generic `Fusion.fold-hom`, here proved directly
--     on the concrete fold);
--   * `Initiality`, Lambek's lemma and the translation fusion are available for
--     `DiagramC S`, e.g. rendering after `translate` along a container morphism.

module Slides.Diagram.Syntax.Properties.Generic where

open import Level using (0ℓ; Lift)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_,_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Data.Container.Relation.Binary.Pointwise using () renaming (_,_ to _,ₚ_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl)

open import Categories.Functor.Algebra using (F-Algebra)

open import Container.FreeMonad.Algebraic using (module Alg)
open import Container.Interpret using (module Initiality)
open import Slides.Diagram.Syntax using (arity; DiagramC; Dia; Algebra; fold)

module For (S : Set) where
  module G = Alg 0ℓ 0ℓ (DiagramC S)
  open Initiality 0ℓ 0ℓ (DiagramC S) using (⊥ˢ; empty)

  -- handlers that respect pointwise-equal children
  Congruent : (A : Setoid 0ℓ 0ℓ) → Algebra S (Setoid.Carrier A) → Set
  Congruent A α = ∀ o {k k′ : arity o → Setoid.Carrier A} →
                  (∀ i → Setoid._≈_ A (k i) (k′ i)) → Setoid._≈_ A (α o k) (α o k′)

  module _ (A : Setoid 0ℓ 0ℓ) where
    private module A = Setoid A

    -- the `⟦ DiagramC S ⟧`-algebra on `A`
    toAlgebra : (α : Algebra S A.Carrier) → Congruent A α → F-Algebra G.F
    toAlgebra α c = record
      { A = A
      ; α = record
          { to   = λ { (o , k) → α o k }
          ; cong = λ { {_ , _} {_ , _} (refl ,ₚ k≈) → c _ k≈ } } }

    -- a diagram as a program with leaves in the empty setoid
    embed : Dia S → DiagramC S ⋆ Lift 0ℓ ⊥
    embed (pure ())
    embed (impure (o , k)) = impure (o , λ i → embed (k i))

    -- the concrete fold is the generic one
    fold-agrees : (α : Algebra S A.Carrier) (c : Congruent A α) (d : Dia S) →
                  fold α d A.≈ G.fold (toAlgebra α c) (empty A) (embed d)
    fold-agrees α c (pure ())
    fold-agrees α c (impure (o , k)) = c o (λ i → fold-agrees α c (k i))

    -- Folding commutes with a map that commutes with the handlers
    module _ (B : Setoid 0ℓ 0ℓ) (α : Algebra S A.Carrier) (β : Algebra S (Setoid.Carrier B))
             (cβ : Congruent B β) (h : Func A B)
             (commutes : ∀ o (k : arity o → A.Carrier) → Setoid._≈_ B (h ⟨$⟩ α o k) (β o (λ i → h ⟨$⟩ k i))) where
      fold-hom : ∀ d → Setoid._≈_ B (h ⟨$⟩ fold α d) (fold β d)
      fold-hom (pure ())
      fold-hom (impure (o , k)) = Setoid.trans B (commutes o (λ i → fold α (k i))) (cβ o (λ i → fold-hom (k i)))
