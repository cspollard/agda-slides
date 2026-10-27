{-# OPTIONS --safe --without-K #-}

-- From an animation with discrete templates to the parametric encoding (`Slides.Diagram.Param`).
--
-- As `Slides.Anim.Param`, for animations whose segments are `discrete` or `template`
-- (`Slides.Anim.Syntax.SegBody`; a segment that is a function stays a flipbook, `dparamOf` is
-- `nothing`).  The symbolic scalar is `DExpr` (`Slides.Diagram.Euclid`), the free algebra of all
-- three layers: a continuous template is weakened into it (`weakenE`, an `Ops`-homomorphism), a
-- discrete one is used as it is.  The segments are numbered left to right, the variable of each
-- renamed to its own (`renameD`, a substitution), and the symbolic frames laid out once.
--
-- Agreement (`Slides.Anim.DParam.Properties`): the frame of the animation at tick `k` -- computed in
-- ℕ from the functions -- is the symbolic layout of tick `k` evaluated in ℕ at the assignment
-- `i ↦ (parameter of segment i at tick k)`.  One segment is `dleaf-agrees`: laying the renamed
-- template out symbolically and evaluating it is laying out the template at the segment's own
-- parameter (`Slides.Diagram.Euclid.Properties.Layout.layout-substD`).
--
-- What the page shows.  The page evaluates the formulas in ℕ (`Slides.Anim.Formula.encD`), at
-- the whole tick `k = ⌊τ⌋` of real time `τ`: for `k ≤ τ < k+1` it shows the frame of tick
-- `k`, there is no interpolation (`units` rounds the parameter down, and a discrete body is
-- only defined at whole ticks).  This is the frame the flipbook shows at tick `k`.

module Slides.Anim.DParam where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Container.FreeMonad using (_⋆_)
open import Slides.Diagram.Syntax using (Dia; mapDia)
open import Slides.Diagram.Euclid using (DExpr; dexprOps; renameD; weakenE)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Slides.Diagram.Param using (DParam; dparam)
open import Slides.Anim.Syntax
open import Slides.Anim.Param using (seqAll; Leaf; leaf; leavesWith; symbolicFramesWith; segmentsOf)

-- a segment placed in an animation (`Slides.Anim.Param.Leaf` over `DExpr`)
DLeaf : Set
DLeaf = Leaf DExpr

dleafOf : ℕ → ℕ → Seg ℕ → Maybe DLeaf
dleafOf i t₀ s with content s
... | template d  = just (leaf i t₀ (track s) (mapDia weakenE d))
... | discrete d  = just (leaf i t₀ (track s) d)
... | blackBox _  = nothing

dleaves : ℕ → ℕ → Anim ℕ (Seg ℕ) → Maybe (ℕ × (AnimC ⋆ DLeaf))
dleaves = leavesWith dleafOf

-- the template of a leaf, with its variable renamed to the leaf's own
dinstantiate : DLeaf → Dia (DExpr ℕ)
dinstantiate l = mapDia (renameD (λ _ → Leaf.idx l)) (Leaf.tmpl l)

dsymbolicFrames : (AnimC ⋆ DLeaf) → List (Dia (DExpr ℕ))
dsymbolicFrames = symbolicFramesWith dinstantiate

dmkParam : (AnimC ⋆ DLeaf) → DParam
dmkParam a = dparam (map (LayoutWith.layout dexprOps) (dsymbolicFrames a)) (segmentsOf a)

-- no frames: the empty frame is not a parametric one
dnonEmpty : DParam → Maybe DParam
dnonEmpty p with DParam.ticks p
... | []    = nothing
... | _ ∷ _ = just p

-- the parametric encoding of acts played one after the other, if every segment is a template
-- of one kind or the other
dparamOf : List (Anim ℕ (Seg ℕ)) → Maybe DParam
dparamOf acts =
  seqAll acts Maybe.>>= λ a →
  dleaves 0 0 a Maybe.>>= λ { (_ , l) →
  dnonEmpty (dmkParam l) }
