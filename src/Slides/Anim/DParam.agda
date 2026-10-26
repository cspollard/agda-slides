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
-- Agreement (`Slides.Anim.DParamCorrect`): the frame of the animation at tick `k` -- computed in
-- ℕ from the functions -- is the symbolic layout of tick `k` evaluated in ℕ at the assignment
-- `i ↦ (parameter of segment i at tick k)`.  One segment is `dleaf-agrees`: laying the renamed
-- template out symbolically and evaluating it is laying out the template at the segment's own
-- parameter (`Slides.Diagram.EuclidNatural.layout-substD`).
--
-- What the page shows.  The page evaluates the formulas in ℕ (`Slides.Anim.Formula.encD`), at
-- the whole tick `k = ⌊τ⌋` of real time `τ`: for `k ≤ τ < k+1` it shows the frame of tick
-- `k`, there is no interpolation (`units` rounds the parameter down, and a discrete body is
-- only defined at whole ticks).  This is the frame the flipbook shows at tick `k`.

module Slides.Anim.DParam where

open import Data.List using (List; []; _∷_; _++_; map; replicate)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Fin using (zero; suc)
open import Data.Unit using (⊤)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Rational using (ℚ)

open import Slides.Diagram.Syntax using (Dia; atop; mapDia)
open import Slides.Diagram.Euclid using (DExpr; dexprOps; evalD; natD; renameD; weakenE)
open import Slides.Diagram.EuclidNatural using (layout-substD)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Slides.Diagram.Scalar using (natOps)
open import Slides.Diagram.Param using (DParam; dparam)
import Slides.Anim.Track as T
open import Slides.Anim.Syntax
open import Slides.Anim.Timeline using (timeline)
open import Slides.Anim.Param using (pieces; seqAll; Leaf)

-- a segment placed in an animation
record DLeaf : Set where
  constructor dleaf
  field
    idx    : ℕ          -- its variable
    start  : ℕ          -- the tick it starts at
    track  : T.Track ℚ  -- its parameter over time
    tmpl   : Dia (DExpr ⊤)

dleafOf : ℕ → ℕ → Seg ℕ → Maybe DLeaf
dleafOf i t₀ s with content s
... | template d  = just (dleaf i t₀ (track s) (mapDia weakenE d))
... | discrete d  = just (dleaf i t₀ (track s) d)
... | blackBox _  = nothing

dleaves : ℕ → ℕ → Anim ℕ (Seg ℕ) → Maybe (ℕ × (AnimC ⋆ DLeaf))
dleaves i t₀ (pure s)               = Maybe.map (λ l → suc i , pure l) (dleafOf i t₀ s)
dleaves i t₀ (impure (Seq , k))     =
  dleaves i t₀ (k zero) Maybe.>>= λ { (i₁ , a) →
  dleaves i₁ (t₀ + dur (k zero)) (k (suc zero)) Maybe.>>= λ { (i₂ , b) →
  just (i₂ , a ⨾ b) } }
dleaves i t₀ (impure (Par , k))     =
  dleaves i t₀ (k zero) Maybe.>>= λ { (i₁ , a) →
  dleaves i₁ t₀ (k (suc zero)) Maybe.>>= λ { (i₂ , b) →
  just (i₂ , a ∥ᵃ b) } }

-- the template of a leaf, with its variable renamed to the leaf's own
dinstantiate : DLeaf → Dia (DExpr ℕ)
dinstantiate l = mapDia (renameD (λ _ → DLeaf.idx l)) (DLeaf.tmpl l)

dsymbolicFrames : (AnimC ⋆ DLeaf) → List (Dia (DExpr ℕ))
dsymbolicFrames = timeline atop (λ l → replicate (T.dur (DLeaf.track l)) (dinstantiate l))

dsegmentsOf : (AnimC ⋆ DLeaf) → List (ℕ × List (T.Piece ℚ))
dsegmentsOf = foldA (λ l → (DLeaf.start l , pieces (DLeaf.track l)) ∷ []) _++_ _++_

dmkParam : (AnimC ⋆ DLeaf) → DParam
dmkParam a = dparam (map (LayoutWith.layout dexprOps) (dsymbolicFrames a)) (dsegmentsOf a)

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

------------------------------------------------------------------------
-- Agreement for one segment

-- Laying a segment's renamed template out symbolically and evaluating it at an assignment is
-- laying out the template at the segment's own parameter there.
dleaf-agrees : ∀ (l : DLeaf) (ρ : ℕ → ℕ) →
  LayoutWith.layout natOps (mapDia (evalD natD ρ) (dinstantiate l))
  ≡ LayoutWith.layout natOps (mapDia (evalD natD (λ _ → ρ (DLeaf.idx l))) (DLeaf.tmpl l))
dleaf-agrees l ρ = layout-substD natD (λ _ → pure (DLeaf.idx l)) ρ (DLeaf.tmpl l)
