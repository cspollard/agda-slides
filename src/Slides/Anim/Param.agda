{-# OPTIONS --safe --without-K #-}

-- From an animation of templates to the parametric encoding (`Slides.Diagram.Param`).
--
-- Every segment of the animation must be a template (`Slides.Anim.Syntax.SegBody`); if one
-- is a function the animation stays a flipbook (`paramOf` is `nothing`).
--
-- The segments are numbered left to right (`leaves`), each with the tick it starts at.
-- The template of segment `i` has one variable, its parameter, renamed to the variable
-- `i` (`rename`, a substitution), so that segments played together keep independent
-- parameters.  The symbolic frames are then exactly the frames of the animation, with
-- `atop` for `Par` and concatenation for `Seq` (`Slides.Anim.Timeline.timeline`), over
-- the free scalar; each is laid out once.
--
-- Agreement.  The frame the page shows at real time `τ`, `k ≤ τ < k+1`, is the symbolic
-- layout of tick `k` evaluated *in ℚ* at the assignment `i ↦ (sample of segment i's track at
-- τ - its start)`: `Slides.Anim.Continuous.frameAt`.  For one segment that is `leaf-agreesℚ`
-- (and `leaf-agrees` for the discrete frames at ℕ): laying the renamed template out
-- symbolically and evaluating is laying out the template at the segment's own parameter
-- (`Slides.Diagram.LayoutNatural.layout-substWith`).  `atop` and the timeline are the same on
-- both sides, so the whole frame agrees; that last assembly (an induction over the animation
-- tracking tick offsets and the fractional part of `τ`) is checked by the browser test over
-- the `animref` deck (`tests/browser/anim-ref.mjs`), not proved here.
--
-- The page gets the track's pieces, not samples: its size does not grow with the ticks.

module Slides.Anim.Param where

open import Data.List using (List; []; _∷_; _++_; map; replicate; length; applyUpTo)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Fin using (zero; suc)
open import Data.Unit using (⊤; tt)
open import Function using (id)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Slides.Diagram.Draw using (Layout)
open import Slides.Diagram.Syntax using (Dia; atop; mapDia)
open import Slides.Diagram.Expr using (Expr; exprOps; eval; evalWith; rename; subst; var)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Slides.Diagram.Scalar using (natOps; ratOps)
open import Data.Rational using (ℚ)
open import Slides.Diagram.Param using (Param; param)
open import Slides.Diagram.LayoutNatural using (layout-subst; layout-substWith)
import Slides.Anim.Track as T
open import Slides.Anim.Syntax
open import Slides.Anim.Timeline using (timeline)

-- a template segment placed in an animation
record Leaf : Set where
  constructor leaf
  field
    idx    : ℕ          -- its variable
    start  : ℕ          -- the tick it starts at
    track  : T.Track ℚ  -- its parameter over time
    tmpl   : Dia (Expr ⊤)

-- the pieces of a track, in order
pieces : ∀ {A} → T.Track A → List (T.Piece A)
pieces = T.foldT (λ p → p ∷ []) _++_

leafOf : ℕ → ℕ → Seg ℕ → Maybe Leaf
leafOf i t₀ s with content s
... | template d  = just (leaf i t₀ (track s) d)
... | blackBox _  = nothing

-- number the segments, from `i`, and give each its start tick, from `t₀`; the result is
-- the next number and the same animation over leaves
leaves : ℕ → ℕ → Anim ℕ (Seg ℕ) → Maybe (ℕ × (AnimC ⋆ Leaf))
leaves i t₀ (pure s)               = Maybe.map (λ l → suc i , pure l) (leafOf i t₀ s)
leaves i t₀ (impure (Seq , k))     =
  leaves i t₀ (k zero) Maybe.>>= λ { (i₁ , a) →
  leaves i₁ (t₀ + dur (k zero)) (k (suc zero)) Maybe.>>= λ { (i₂ , b) →
  just (i₂ , a ⨾ b) } }
leaves i t₀ (impure (Par , k))     =
  leaves i t₀ (k zero) Maybe.>>= λ { (i₁ , a) →
  leaves i₁ t₀ (k (suc zero)) Maybe.>>= λ { (i₂ , b) →
  just (i₂ , a ∥ᵃ b) } }

-- the template of a leaf, with its variable renamed to the leaf's own
instantiate : Leaf → Dia (Expr ℕ)
instantiate l = mapDia (rename (λ _ → Leaf.idx l)) (Leaf.tmpl l)

-- the symbolic frames: the frames of the animation, over the free scalar
symbolicFrames : (AnimC ⋆ Leaf) → List (Dia (Expr ℕ))
symbolicFrames = timeline atop (λ l → replicate (T.dur (Leaf.track l)) (instantiate l))

segmentsOf : (AnimC ⋆ Leaf) → List (ℕ × List (T.Piece ℚ))
segmentsOf = foldA (λ l → (Leaf.start l , pieces (Leaf.track l)) ∷ []) _++_ _++_

mkParam : (AnimC ⋆ Leaf) → Param
mkParam a = param (map (LayoutWith.layout exprOps) (symbolicFrames a)) (segmentsOf a)

-- acts one after the other
seqAll : List (Anim ℕ (Seg ℕ)) → Maybe (Anim ℕ (Seg ℕ))
seqAll []           = nothing
seqAll (a ∷ [])     = just a
seqAll (a ∷ b ∷ as) = Maybe.map (a ⨾_) (seqAll (b ∷ as))

-- no frames: the empty frame is not a parametric one
nonEmptyParam : Param → Maybe Param
nonEmptyParam p with Param.ticks p
... | []    = nothing
... | _ ∷ _ = just p

-- the parametric encoding of acts played one after the other, if every segment is a template
paramOf : List (Anim ℕ (Seg ℕ)) → Maybe Param
paramOf acts =
  seqAll acts Maybe.>>= λ a →
  leaves 0 0 a Maybe.>>= λ { (_ , l) →
  nonEmptyParam (mkParam l) }

------------------------------------------------------------------------
-- Agreement for one segment

-- Laying a segment's renamed template out symbolically and evaluating it at an assignment
-- is laying out the template at the segment's own parameter there.
leaf-agrees : ∀ (l : Leaf) (ρ : ℕ → ℕ) →
  LayoutWith.layout natOps (mapDia (eval ρ) (instantiate l))
  ≡ LayoutWith.layout natOps (mapDia (eval (λ _ → ρ (Leaf.idx l))) (Leaf.tmpl l))
leaf-agrees l ρ = layout-subst (λ _ → var (Leaf.idx l)) ρ (Leaf.tmpl l)

-- the same in ℚ, the scalar of the continuous player
leaf-agreesℚ : ∀ (l : Leaf) (ρ : ℕ → ℚ) →
  LayoutWith.layout ratOps (mapDia (evalWith ratOps ρ) (instantiate l))
  ≡ LayoutWith.layout ratOps (mapDia (evalWith ratOps (λ _ → ρ (Leaf.idx l))) (Leaf.tmpl l))
leaf-agreesℚ l ρ = layout-substWith ratOps (λ _ → var (Leaf.idx l)) ρ (Leaf.tmpl l)
