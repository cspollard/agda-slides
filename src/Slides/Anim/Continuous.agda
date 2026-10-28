{-# OPTIONS --safe --without-K #-}

-- Continuous time for template animations: the specification the page implements.
--
-- An animation of templates (every segment a `SegBody.template`, `Slides.Anim.Syntax`) is
-- played in real time `τ`, measured in ticks.  The page receives each segment's track as data
-- and the symbolic layout (`Slides.Anim.Param`); this module says what it must draw.
--
-- The formulation.
--
--   * Time is a `ℚ`.  A track sampled at real time is `sampleAt`, the algebra of the track's
--     free monad into `Timed A = ℕ × (ℚ → A)` (the duration and a function of time): a piece
--     is `Lerp (progress e (τ/d))` (`Slides.Anim.Track`, unchanged), and `Seq` is `seqAt`,
--     which switches to the second function at the boundary and offsets its time by the first
--     duration.  Pieces are half-open, so the sample is right-continuous: at a boundary the
--     later piece holds (`seqAt-boundary`), and a piece holds its `to` once over
--     (`piece-hold`).  Time starts at 0; a segment shows nothing outside `[0, ticks)`.
--   * The parameter of a template is a ℚ and is *not* floored: `instQ d q` evaluates the
--     template's `OExpr ⊤` in `ratO` with `t := q`.  `evalO ratO ρ` is an `Ops`-homomorphism
--     (`evalO-hom`) and layout is natural along it (`layout-natural`), so the continuous frame is
--     the evaluation in ℚ of the very symbolic layout the page is sent.  There is no `units`
--     (floor) in the semantics of a plain template, the page draws fractional coordinates; the
--     floor belongs to the discrete reading `bodyAt` (`units q`) and to discrete bodies, which
--     are templates that hold the parameter (`Slides.Anim.Syntax.discrete`: `⌊q⌋` is a node of
--     the formulas, `holdT`).
--   * An animation is `animAt`, the `foldA` of the segments into `Timed (Maybe (Dia ℚ))`:
--     `Par` is `parAt` (the same `τ` on both sides, duration the maximum, frames overlaid with
--     `atop` and a side that is not running contributing nothing, as `Slides.Anim.Timeline.merge`)
--     and `Seq` is `seqAt`.  `frameAt a τ` is the layout in ℚ (`Slides.Diagram.Layout`
--     at `ratOps`) of the diagram running at `τ`.
--
-- Where the discrete (ℕ) and continuous (ℚ) readings differ, honestly.  ℚ's `-` is real
-- subtraction where ℕ's is the monus, ℚ's percentage is exact where ℕ's rounds down, and the
-- discrete parameter is floored.  So `100 ⊖ t` is negative in ℚ once `t > 100` (the frame has
-- a negative size, which `Slides.Diagram.Place.Properties.Valid` excludes; a template should stay in the
-- domain where its differences are non-negative) and a ℕ frame at the floor of a fractional
-- sample differs from the ℚ frame at the sample itself.
--
-- Proved in `Slides.Anim.Continuous.Properties`.
--   * `sampleAt-ι`: at whole ticks the continuous sample of a track is the discrete one
--     (`Slides.Anim.Track.sample`), exactly; so is `leafAt-ι` for a segment's frame.
--   * `leaf-tick`: if moreover the sample is a whole number and the template's layout is exact
--     (`Slides.Diagram.Ordered.Properties.Faithful.FaithfulO`: differences with minuend ≥ subtrahend, percentages that
--     divide), the continuous frame at tick `k` is the discrete frame sent through `ι`.
--   * `parAt-time`, `parAt-dur`, `seqAt-before`, `seqAt-after`, `seqAt-boundary`: `Par` is the
--     same `τ` on both sides and `Seq` offsets time by the duration; `animAt-dur`: the
--     duration is `Slides.Anim.Syntax.dur`.
--   * `piece-hold`, `piece-start`: the sample is `from` at a piece's start and `to` after its end.
--
-- Not proved: that the page's JavaScript (floating point easings, the formula evaluator)
-- computes `frameAt`; it is tested at sampled times against the exact values
-- (`tests/browser/anim-ref.mjs`).  The assembly over a whole timeline at whole ticks is
-- `Slides.Anim.Assembly.Continuous`; not proved is that for fractional `τ`, `k < τ < k+1`,
-- `frameAt a τ` is the symbolic layout of tick `k` evaluated at each segment's sample at
-- `τ - start`.

module Slides.Anim.Continuous where

open import Data.Bool using (Bool; not; _∧_; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Unit using (⊤)
open import Data.Integer as ℤ using (+_)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; _/_)
open import Data.Fin using (zero; suc)

open import Slides.Diagram.NatQ using (ι)

import Slides.Anim.Track as Tr
open import Slides.Time using (module Sem)
open import Slides.Time.Rat using (ratClock)
open import Slides.Anim.Syntax using (Anim; Seg; SegBody; foldA; track; content; template; blackBox)
open import Slides.Diagram.Draw using (Layout)
open import Slides.Diagram.Ordered using (OExpr; evalO; ratO; _<ᵇℚ_)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Slides.Diagram.Scalar using (ratOps)
open import Slides.Diagram.Syntax using (Dia; atop; mapDia)

------------------------------------------------------------------------
-- Real time on a track

-- how far through `d` ticks the time `τ` is (clamped above; a negative time never reaches a
-- piece, see `leafAt`)
ratioAt : ℚ → ℕ → ℚ
ratioAt τ zero    = 1ℚ
ratioAt τ (suc d) = if τ <ᵇℚ ι (suc d) then τ ℚ.* (+ 1 / suc d) else 1ℚ

pieceAt : ∀ {A} → Tr.Lerp A → Tr.Piece A → ℚ → A
pieceAt L (Tr.piece d a b e) τ = Tr.Lerp.lerp L (Tr.progress e (ratioAt τ d)) a b

-- the temporal skeleton, read in the clock ℚ (`Slides.Time`: `Timed`, `seqAt`, `parAt`)
open Sem ratClock public

sampleAt : ∀ {A} → Tr.Lerp A → Tr.Track A → Timed A
sampleAt L = Tr.foldT (λ p → Tr.ticks p , pieceAt L p) seqAt

------------------------------------------------------------------------
-- Template segments in real time

-- A template at the value `q` of its parameter: the sizes are evaluated *in ℚ*, with
-- `t := q` itself (the discrete reading `bodyAt` puts `fromℕ (units q)`, floored).
instQ : Dia (OExpr ⊤) → ℚ → Dia ℚ
instQ d q = mapDia (evalO ratO (λ _ → q)) d

-- a segment is running on `0 ≤ τ < ticks`; there its template is at the track's value
leafAt : Tr.Track ℚ → Dia (OExpr ⊤) → Timed (Maybe (Dia ℚ))
leafAt tr d = proj₁ s , λ τ → if (0ℚ ℚ.≤ᵇ τ) ∧ (τ <ᵇℚ ι (proj₁ s)) then just (instQ d (proj₂ s τ)) else nothing
  where s = sampleAt Tr.ℚLerp tr

-- the timed frames of an animation all of whose segments are templates
bodyAt′ : Tr.Track ℚ → SegBody ℕ → Maybe (Timed (Maybe (Dia ℚ)))
bodyAt′ tr (template d) = just (leafAt tr d)
bodyAt′ tr (blackBox _) = nothing

segAt : Seg ℕ → Maybe (Timed (Maybe (Dia ℚ)))
segAt s = bodyAt′ (track s) (content s)

-- both parts, or nothing
lift2 : ∀ {A : Set} → (A → A → A) → Maybe A → Maybe A → Maybe A
lift2 = Maybe.zipWith

animAt : Anim ℕ (Seg ℕ) → Maybe (Timed (Maybe (Dia ℚ)))
animAt a = foldA segAt (lift2 seqAt) (lift2 (parAt atop)) a

-- The frame at real time `τ`: the layout, in ℚ, of the template segments running at `τ`.
-- `nothing` when some segment is not a template, or none is running at `τ`.
frameAt : Anim ℕ (Seg ℕ) → ℚ → Maybe (Layout ℚ)
frameAt a τ with animAt a
... | nothing        = nothing
... | just (_ , f)   = Maybe.map (LayoutWith.layout ratOps) (f τ)
