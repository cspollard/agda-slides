{-# OPTIONS --safe --without-K #-}

-- The assembly of whole frames for discrete templates: the symbolic frames of
-- `Slides.Anim.DParam` are the frames of the animation (cf. `Slides.Anim.Param.Properties`, for
-- continuous templates read in ℕ).
--
-- Statement.  Let `a` be an animation whose segments are `template` or `discrete` (so that
-- `dleaves 0 0 a ≡ just (i′ , l)`).  For every tick `k < dur a`,
--
--     layout_ℕ (frame k of  timeline atop (frames natOps) a)
--       ≡  mapLayout (evalD natD ρ) (layout_DExpr (symbolic frame k))
--
-- for every assignment `ρ` such that every leaf running at tick `k` has
-- `ρ (idx) ≡ units (sample of its track at that tick)` (`DGoodL l k ρ`).  The right-hand side
-- is what the page computes: the formulas of the tick, read in ℕ (`Slides.Anim.Formula.encD-semN`
-- says that the shipped, folded formula is `evalD natD ρ`), and the left is the frame the
-- flipbook shows.  The proof is the one of `Slides.Anim.Param.Properties`, the instance of
-- `Slides.Anim.Assembly.Leaf` for `Expr`, with `Slides.Diagram.Euclid.Properties.Layout` for one segment: the
-- Euclidean operations never reach the layout, they only live in the leaves' formulas.  So the
-- tick-by-tick theorem (`discrete-assemblyD`), the numbering of the leaves and the canonical
-- assignment (`assembly-canonical`) are the generic ones.
--
-- `DGoodL` is satisfiable by `i ↦ (parameter of segment i at tick k)` (`canonical-good`,
-- `assembly-canonical`, from the generic module).

module Slides.Anim.DParam.Properties where

open import Data.Bool using ()
open import Data.List using (replicate)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; _+_; _<ᵇ_)
open import Data.Product using (_,_)
open import Data.Unit using ()
open import Data.Container.FreeMonad using (pure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Slides.Diagram.Draw using (Layout; mapLayout)
open import Slides.Diagram.Syntax using (Dia; mapDia)
open import Slides.Diagram.Euclid
open import Slides.Diagram.Euclid.Properties
open import Slides.Diagram.Euclid.Properties.Layout using (layout-evalD; layout-weakenE; layout-substD)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Slides.Diagram.Scalar using (natOps)
open import Slides.Diagram.Layout.Properties using (atop-natural)
import Slides.Anim.Track as T
open import Slides.Anim.Syntax
open import Slides.Anim.Timeline using (frames)
open import Slides.Anim.Param using (Leaf)
open import Slides.Anim.DParam
import Slides.Anim.Assembly.Leaf as LA

private
  layoutℕ : Dia ℕ → Layout ℕ
  layoutℕ = LayoutWith.layout natOps

  layoutD : Dia (DExpr ℕ) → Layout (DExpr ℕ)
  layoutD = LayoutWith.layout dexprOps

------------------------------------------------------------------------
-- One segment

-- Laying a segment's renamed template out symbolically and evaluating it at an assignment is
-- laying out the template at the segment's own parameter there.
dleaf-agrees : ∀ (l : DLeaf) (ρ : ℕ → ℕ) →
  LayoutWith.layout natOps (mapDia (evalD natD ρ) (dinstantiate l))
  ≡ LayoutWith.layout natOps (mapDia (evalD natD (λ _ → ρ (Leaf.idx l))) (Leaf.tmpl l))
dleaf-agrees l ρ = layout-substD natD (λ _ → pure (Leaf.idx l)) ρ (Leaf.tmpl l)

-- a symbolic frame is interpreted by evaluating its layout in ℕ; `atop` is `atop` because layout
-- is natural along `evalD`, an `Ops`-homomorphism
open LA.Over DExpr (λ y ρ → mapLayout (evalD natD ρ) (layoutD y))
  (λ x y ρ → sym (atop-natural dexprOps natOps (evalD natD ρ) (evalD-hom-ℕ ρ) (layoutD x) (layoutD y)))
  (λ r d → mapDia (evalD natD (λ _ → r)) d) dinstantiate
  (λ l ρ → trans (layout-evalD natD ρ (dinstantiate l)) (dleaf-agrees l ρ))
  public

------------------------------------------------------------------------
-- The whole animation

private
  dleafOf-idx : ∀ i t₀ s l → dleafOf i t₀ s ≡ just l → Leaf.idx l ≡ i
  dleafOf-idx i t₀ (seg tr (template d)) _ refl = refl
  dleafOf-idx i t₀ (seg tr (discrete d)) _ refl = refl
  dleafOf-idx i t₀ (seg tr (blackBox f)) _ ()

  dleafAgree : ∀ i t₀ s l → dleafOf i t₀ s ≡ just l →
               Agree (LeafGood l) t₀ (frames natOps s) (replicate (T.dur (Leaf.track l)) (dinstantiate l))
  dleafAgree i t₀ (seg tr (template d)) _ refl =
    leaf-Agree (template d) i t₀ tr (mapDia weakenE d) (λ r → sym (layout-weakenE natD (λ _ → units r) d))
  dleafAgree i t₀ (seg tr (discrete d)) _ refl = leaf-Agree (discrete d) i t₀ tr d (λ r → refl)
  dleafAgree i t₀ (seg tr (blackBox f)) _ ()

open Induction dleafOf dleafOf-idx dleafAgree public

-- the discrete reading of the statement and of the leaves' condition, under their names here
DLeafGood = LeafGood
DGoodL    = GoodL
dleaves-agree = leaves-agree
discrete-assemblyD = assembly
