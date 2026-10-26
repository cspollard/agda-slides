{-# OPTIONS --safe --without-K #-}

-- Layout of discrete templates is natural along evaluation.
--
-- The layout (`Slides.Diagram.Place`) takes sums, differences, maxima and percentages of its
-- scalars and nothing else: it never compares or divides.  So it only uses the first two layers
-- of a scalar (`Ops`), and the Euclidean operations (`Slides.Diagram.Euclid`) occur only
-- *inside* the scalars, in the formulas at the leaves.  Hence the naturality theorem of
-- `Slides.Diagram.Layout.Properties` applies unchanged along `evalD`, which is an `Ops`-homomorphism
-- (`Euclid.evalD-hom`); this module states the consequences the discrete assembly uses:
--
--   * `layout-evalD`: a diagram over discrete formulas, laid out symbolically and evaluated at
--     `ρ`, is the layout of the diagram with those formulas evaluated;
--   * `layout-substD`: laying out a template whose variables are replaced by formulas and
--     evaluating at `ρ` is laying it out at the evaluated substitution (as `layout-substWith`);
--   * `layout-weakenE`: a continuous template (`Expr`) weakened to a discrete one lays out, when
--     evaluated in ℕ, as the template does (it is `weakenE-hom`, an `Ops`-homomorphism, composed
--     with `evalD`).

module Slides.Diagram.Euclid.Properties.Layout where

open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; trans)

open import Slides.Diagram.Scalar using ()
open import Slides.Diagram.Syntax using (Dia; mapDia)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Slides.Diagram.Expr using (Expr; exprOps; evalWith)
open import Slides.Diagram.Expr.Properties using (evalWith-hom)
open import Slides.Diagram.Euclid
open import Slides.Diagram.Euclid.Properties
open import Slides.Diagram.Layout.Properties using (layout-natural; mapLayout-∘; mapLayout-cong)
open import Slides.Diagram.Draw using (mapLayout)

layout-evalD : ∀ {V S} (D : DiscreteOps S) (ρ : V → S) (d : Dia (DExpr V)) →
  mapLayout (evalD D ρ) (LayoutWith.layout dexprOps d)
  ≡ LayoutWith.layout (DiscreteOps.ops D) (mapDia (evalD D ρ) d)
layout-evalD D ρ = layout-natural dexprOps (DiscreteOps.ops D) (evalD D ρ) (evalD-hom D ρ)

layout-substD : ∀ {V W S} (D : DiscreteOps S) (σ : V → DExpr W) (ρ : W → S) (d : Dia (DExpr V)) →
  LayoutWith.layout (DiscreteOps.ops D) (mapDia (evalD D ρ) (mapDia (substD σ) d))
  ≡ LayoutWith.layout (DiscreteOps.ops D) (mapDia (evalD D (λ v → evalD D ρ (σ v))) d)
layout-substD D σ ρ d =
  trans (sym (layout-evalD D ρ (mapDia (substD σ) d)))
  (trans (cong (mapLayout (evalD D ρ)) (sym (layout-natural dexprOps dexprOps (substD σ) (substD-hom σ) d)))
  (trans (mapLayout-∘ (evalD D ρ) (substD σ) (LayoutWith.layout dexprOps d))
  (trans (mapLayout-cong (evalD-substD D ρ σ) (LayoutWith.layout dexprOps d))
         (layout-evalD D (λ v → evalD D ρ (σ v)) d))))

layout-weakenE : ∀ {V S} (D : DiscreteOps S) (ρ : V → S) (d : Dia (Expr V)) →
  LayoutWith.layout (DiscreteOps.ops D) (mapDia (evalD D ρ) (mapDia weakenE d))
  ≡ LayoutWith.layout (DiscreteOps.ops D) (mapDia (evalWith (DiscreteOps.ops D) ρ) d)
layout-weakenE D ρ d =
  trans (sym (layout-evalD D ρ (mapDia weakenE d)))
  (trans (cong (mapLayout (evalD D ρ)) (sym (layout-natural exprOps dexprOps weakenE weakenE-hom d)))
  (trans (mapLayout-∘ (evalD D ρ) weakenE (LayoutWith.layout exprOps d))
  (trans (mapLayout-cong (evalD-weaken D ρ) (LayoutWith.layout exprOps d))
         (layout-natural exprOps (DiscreteOps.ops D) (evalWith (DiscreteOps.ops D) ρ)
                         (evalWith-hom (DiscreteOps.ops D) ρ) d))))
