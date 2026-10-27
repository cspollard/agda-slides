{-# OPTIONS --safe --without-K #-}

-- From an animation of templates to the parametric encoding (`Slides.Diagram.Param`).
--
-- Every segment of the animation must be a template (`Slides.Anim.Syntax.SegBody`); if one
-- is a function the animation stays a flipbook (`paramOf` is `nothing`).
--
-- The segments are numbered left to right (`leaves`), each with the tick it starts at.
-- The template of segment `i` has one variable, its parameter, renamed to the variable
-- `i` (`substO`, a substitution), so that segments played together keep independent
-- parameters.  The symbolic frames are then exactly the frames of the animation, with
-- `atop` for `Par` and concatenation for `Seq` (`Slides.Anim.Timeline.timeline`), over
-- the free scalar; each is laid out once.  A discrete segment is a template too
-- (`Slides.Anim.Syntax.discrete`), so one pipeline ships both.
--
-- Agreement.  The frame the page shows at real time `τ`, `k ≤ τ < k+1`, is the symbolic
-- layout of tick `k` evaluated *in ℚ* at the assignment `i ↦ (sample of segment i's track at
-- τ - its start)`: `Slides.Anim.Continuous.frameAt`.  For one segment that is `leaf-agrees`:
-- laying the renamed template out symbolically and evaluating is laying out the template at the
-- segment's own parameter (`Slides.Diagram.Ordered.Properties.Laws.layout-substO`).  `atop` and
-- the timeline are the same on both sides, so the whole frame agrees: that assembly, an induction
-- over the animation tracking tick offsets, is `Slides.Anim.Param.Properties` (in ℕ) and
-- `Slides.Anim.Assembly.Continuous` (ℚ against ℕ, at whole ticks); fractional `τ` is checked by
-- the browser test over the `animref` deck (`tests/browser/anim-ref.mjs`), not proved.
--
-- The page gets the track's pieces, not samples: its size does not grow with the ticks.

module Slides.Anim.Param where

open import Data.List using (List; []; _∷_; _++_; map; replicate)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Fin using (zero; suc)
open import Data.Unit using (⊤)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)

open import Slides.Diagram.Syntax using (Dia; atop; mapDia)
open import Slides.Diagram.Ordered using (OExpr; termOps; substO)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Data.Rational using (ℚ)
open import Slides.Diagram.Param using (Param; param)
import Slides.Anim.Track as T
open import Slides.Anim.Syntax
open import Slides.Anim.Timeline using (timeline)

-- a template segment placed in an animation; `E` is the language of its template's numbers
-- (`OExpr`, `Slides.Diagram.Ordered`; discrete templates are templates, `Slides.Anim.Syntax.discrete`)
record Leaf (E : Set → Set) : Set where
  constructor leaf
  field
    idx    : ℕ          -- its variable
    start  : ℕ          -- the tick it starts at
    track  : T.Track ℚ  -- its parameter over time
    tmpl   : Dia (E ⊤)

-- the pieces of a track, in order
pieces : ∀ {A} → T.Track A → List (T.Piece A)
pieces = T.foldT (λ p → p ∷ []) _++_

leafOf : ℕ → ℕ → Seg ℕ → Maybe (Leaf OExpr)
leafOf i t₀ s with content s
... | template d  = just (leaf i t₀ (track s) d)
... | blackBox _  = nothing

-- number the segments, from `i`, and give each its start tick, from `t₀`; the result is
-- the next number and the same animation over leaves
leavesWith : ∀ {L : Set} → (ℕ → ℕ → Seg ℕ → Maybe L) → ℕ → ℕ → Anim ℕ (Seg ℕ) → Maybe (ℕ × (AnimC ⋆ L))
leavesWith leafOf i t₀ (pure s)               = Maybe.map (λ l → suc i , pure l) (leafOf i t₀ s)
leavesWith leafOf i t₀ (impure (Seq , k))     =
  leavesWith leafOf i t₀ (k zero) Maybe.>>= λ { (i₁ , a) →
  leavesWith leafOf i₁ (t₀ + dur (k zero)) (k (suc zero)) Maybe.>>= λ { (i₂ , b) →
  just (i₂ , a ⨾ b) } }
leavesWith leafOf i t₀ (impure (Par , k))     =
  leavesWith leafOf i t₀ (k zero) Maybe.>>= λ { (i₁ , a) →
  leavesWith leafOf i₁ t₀ (k (suc zero)) Maybe.>>= λ { (i₂ , b) →
  just (i₂ , a ∥ᵃ b) } }

leaves : ℕ → ℕ → Anim ℕ (Seg ℕ) → Maybe (ℕ × (AnimC ⋆ Leaf OExpr))
leaves = leavesWith leafOf

-- the template of a leaf, with its variable renamed to the leaf's own
instantiate : Leaf OExpr → Dia (OExpr ℕ)
instantiate l = mapDia (substO (λ _ → pure (Leaf.idx l))) (Leaf.tmpl l)

-- the symbolic frames: the frames of the animation, over the free scalar
symbolicFramesWith : ∀ {E : Set → Set} → (Leaf E → Dia (E ℕ)) → (AnimC ⋆ Leaf E) → List (Dia (E ℕ))
symbolicFramesWith inst = timeline atop (λ l → replicate (T.dur (Leaf.track l)) (inst l))

symbolicFrames : (AnimC ⋆ Leaf OExpr) → List (Dia (OExpr ℕ))
symbolicFrames = symbolicFramesWith instantiate

segmentsOf : ∀ {E : Set → Set} → (AnimC ⋆ Leaf E) → List (ℕ × List (T.Piece ℚ))
segmentsOf = foldA (λ l → (Leaf.start l , pieces (Leaf.track l)) ∷ []) _++_ _++_

mkParam : (AnimC ⋆ Leaf OExpr) → Param
mkParam a = param (map (LayoutWith.layout termOps) (symbolicFrames a)) (segmentsOf a)

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
