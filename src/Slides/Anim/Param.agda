{-# OPTIONS --safe --without-K #-}

-- From an animation of segments to the parametric encoding (`Slides.Diagram.Param`).
--
-- The animations that have one are those built from segments (`Slides.Anim.Syntax.seg`) by `Seq`,
-- `Par` and `Delay`; any other `Hold`, `Repeat` or `Drive` has no parametric encoding (`place` is
-- `nothing`) and the animation stays a flipbook.
--
-- The segments are numbered left to right, each with the tick it starts at.  The template of
-- segment `i` has one variable, its parameter, renamed to the variable `i` (`substO`, a
-- substitution), so that segments played together keep independent parameters.  The symbolic scene
-- is the animation with each segment replaced by its renamed template under the segment's window;
-- its frames are *the same reading* (`Slides.Anim.Sample`, the ℕ clock, `atop` for `Par`) over the
-- free scalar, and each is laid out once.  A discrete segment is a template too
-- (`Slides.Anim.Syntax.discrete`), so one pipeline ships both.
--
-- Agreement.  The frame the page shows at real time `τ`, `k ≤ τ < k+1`, is the symbolic layout of
-- tick `k` evaluated *in ℚ* at the assignment `i ↦ (sample of segment i's track at τ - its
-- start)`: `Slides.Anim.Continuous.frameAt`.  For one segment that is `leaf-agrees`: laying the
-- renamed template out symbolically and evaluating is laying out the template at the segment's own
-- parameter (`Slides.Diagram.Ordered.Properties.Laws.layout-substO`).  The rest is an induction over
-- the animation tracking tick offsets: `Slides.Anim.Param.Properties` (in ℕ) and
-- `Slides.Anim.Assembly` (ℚ against ℕ, at whole ticks); fractional `τ` is checked by the browser
-- test over the `animref` deck (`tests/browser/anim-ref.mjs`), not proved.
--
-- The page gets the track's pieces, not samples: its size does not grow with the ticks.

module Slides.Anim.Param where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; suc; _+_; _≟_)
open import Data.Product using (_×_; _,_)
open import Data.Container.FreeMonad using (pure; impure)
open import Data.Fin using (zero; suc)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)

open import Slides.Diagram.Syntax using (Dia; atop; mapDia; spacer)
open import Slides.Diagram.Ordered using (OExpr; termOps; substO; zero′)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Data.Rational using (ℚ)
open import Data.Rational.Properties using () renaming (_≟_ to _≟ᵠ_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Slides.Diagram.Param using (Param; param)
import Slides.Anim.Track as T
open import Slides.Time.Nat using (natClock)
open import Slides.Anim.Syntax
open import Slides.Anim.Sample
open import Slides.Anim.Timeline using (tabulate)

-- a template segment placed in an animation
record Leaf : Set where
  constructor leaf
  field
    idx    : ℕ          -- its variable
    start  : ℕ          -- the tick it starts at
    track  : T.Track ℚ  -- its parameter over time
    tmpl   : Tmpl

-- the pieces of a track, in order
pieces : ∀ {A} → T.Track A → List (T.Piece A)
pieces = T.foldT (λ p → p ∷ []) _++_

-- a segment: the window is the track's duration
segDrive : ℕ → T.Track ℚ → Anim → Maybe (T.Track ℚ × Tmpl)
segDrive n tr (pure d) with n ≟ T.dur tr
... | yes _ = just (tr , d)
... | no _  = nothing
segDrive _ _ _ = nothing

segHold : ℕ → Anim → Maybe (T.Track ℚ × Tmpl)
segHold n (impure (Drive tr , j)) = segDrive n tr (j tt)
segHold _ _ = nothing

segOf : Anim → Maybe (T.Track ℚ × Tmpl)
segOf (impure (Hold n , k)) = segHold n (k tt)
segOf _ = nothing

-- the template of a leaf, with its variable renamed to the leaf's own
instantiate : Leaf → Dia (OExpr ℕ)
instantiate l = mapDia (substO (λ _ → pure (Leaf.idx l))) (Leaf.tmpl l)

-- the symbolic scene of a leaf: its renamed template for as long as the track lasts
symLeaf : Leaf → Scene (Dia (OExpr ℕ))
symLeaf l = hold′ (T.dur (Leaf.track l)) (pure (instantiate l))

-- number the segments, from `i`, and give each its start tick, from `t₀`; the result is the next
-- number, the symbolic scene and the leaves in order
place : ℕ → ℕ → Anim → Maybe (ℕ × Scene (Dia (OExpr ℕ)) × List Leaf)
place i t₀ a with segOf a
... | just (tr , d) = let l = leaf i t₀ tr d in just (suc i , symLeaf l , l ∷ [])
... | nothing with a
...   | impure (Seq , k) =
  place i t₀ (k zero) Maybe.>>= λ { (i₁ , a₁ , l₁) →
  place i₁ (t₀ + dur (k zero)) (k (suc zero)) Maybe.>>= λ { (i₂ , a₂ , l₂) →
  just (i₂ , a₁ ⨾ a₂ , l₁ ++ l₂) } }
...   | impure (Par , k) =
  place i t₀ (k zero) Maybe.>>= λ { (i₁ , a₁ , l₁) →
  place i₁ t₀ (k (suc zero)) Maybe.>>= λ { (i₂ , a₂ , l₂) →
  just (i₂ , a₁ ∥ᵃ a₂ , l₁ ++ l₂) } }
...   | impure (Delay n , k) =
  Maybe.map (λ { (i₁ , a₁ , l₁) → i₁ , delay n a₁ , l₁ }) (place i (t₀ + n) (k tt))
...   | _ = nothing

-- the symbolic frames: the frames of the symbolic scene, over the free scalar (a gap is empty)
symTM : Scene (Dia (OExpr ℕ)) → TM natClock (Dia (OExpr ℕ))
symTM = sample natClock atop (λ _ x → x) (λ _ _ → 0) (λ d → d)

symbolicFrames : Scene (Dia (OExpr ℕ)) → List (Dia (OExpr ℕ))
symbolicFrames s = tabulate (spacer zero′ zero′) (symTM s)

segmentsOf : List Leaf → List (ℕ × List (T.Piece ℚ))
segmentsOf = map (λ l → Leaf.start l , pieces (Leaf.track l))

mkParam : Scene (Dia (OExpr ℕ)) → List Leaf → Param
mkParam s ls = param (map (LayoutWith.layout termOps) (symbolicFrames s)) (segmentsOf ls)

-- acts one after the other
seqAll : List Anim → Maybe Anim
seqAll []           = nothing
seqAll (a ∷ [])     = just a
seqAll (a ∷ b ∷ as) = Maybe.map (a ⨾_) (seqAll (b ∷ as))

-- a track that never moves (every piece starts where it ends): its segment is a held diagram
constant : T.Track ℚ → Bool
constant = T.foldT (λ p → ⌊ T.from p ≟ᵠ T.to p ⌋) _∧_

-- a flipbook (`Slides.Anim.Syntax.flipbook`) has nothing to parametrise: only an animation with a
-- moving parameter is shipped as formulas
moving : List Leaf → Bool
moving []       = false
moving (l ∷ ls) = not (constant (Leaf.track l)) ∨ moving ls

-- no frames: the empty frame is not a parametric one
nonEmptyParam : Param → Maybe Param
nonEmptyParam p with Param.ticks p
... | []    = nothing
... | _ ∷ _ = just p

-- the parametric encoding of acts played one after the other, if every segment is a template
paramOf : List Anim → Maybe Param
paramOf acts =
  seqAll acts Maybe.>>= λ a →
  place 0 0 a Maybe.>>= λ { (_ , s , ls) →
  if moving ls then nonEmptyParam (mkParam s ls) else nothing }
