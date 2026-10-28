{-# OPTIONS --safe --without-K #-}

-- Continuous time for template animations: the specification the page implements.
--
-- An animation (`Slides.Anim.Syntax`) is played in real time `τ`, measured in ticks: this is
-- `Slides.Anim.Sample` read in the clock ℚ (`Slides.Time.Rat`), the same algebra the ℕ clock reads
-- frame by frame (`Slides.Anim.Timeline`).  The page receives each segment's track as data and the
-- symbolic layout (`Slides.Anim.Param`); this module says what it must draw.
--
--   * Time is a `ℚ`.  A track sampled at real time is `sampleAt`, the algebra of the track's free
--     monad into `Timed A = ℕ × (ℚ → A)` (the `Sem` skeleton of the clock): a piece is
--     `Lerp (progress e (τ/d))` (`Slides.Anim.Track`, unchanged; the `Scale` and `Ease` layers have no
--     ℕ reading, so reading a track is the one place the clocks differ: `ratVal` here, `natVal` in
--     `Timeline`), and `Seq` is `seqAt`, which switches to the second function at the boundary and
--     offsets its time by the first duration.  Pieces are half-open, so the sample is
--     right-continuous (`seqAt-boundary`), and a piece holds its `to` once over (`piece-hold`).
--   * The parameter of a template is a ℚ and is *not* floored: the leaf evaluates the template's
--     `OExpr ⊤` in `ratO` with `t := q`.  `evalO ratO ρ` is an `Ops`-homomorphism (`evalO-hom`) and
--     layout is natural along it (`layout-natural`), so the continuous frame is the evaluation in ℚ of
--     the very symbolic layout the page is sent.  There is no `units` (floor) in the semantics of a
--     plain template, the page draws fractional coordinates; the floor belongs to the ℕ clock's
--     `natVal` and to discrete bodies (`Slides.Anim.Syntax.discrete`: `⌊q⌋` is a node of the formulas).
--   * `frameAt a τ` is the layout in ℚ (`Slides.Diagram.Layout` at `ratOps`) of the diagram running
--     at `τ`; `nothing` when none is.
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
--   * `sampleAt-dur`, `piece-hold`, `piece-start`; the laws of `Seq` and `Par` are those of the
--     clock (`Slides.Time.Properties`), at ℚ; the duration of the frames is `dur` (`Sample.Properties`).
--
-- Not proved: that the page's JavaScript (floating point easings, the formula evaluator)
-- computes `frameAt`; it is tested at sampled times against the exact values
-- (`tests/browser/anim-ref.mjs`).  The assembly over a whole animation at whole ticks is
-- `Slides.Anim.Assembly`; not proved is that for fractional `τ`, `k < τ < k+1`,
-- `frameAt a τ` is the symbolic layout of tick `k` evaluated at each segment's sample at
-- `τ - start`.

module Slides.Anim.Continuous where

open import Data.Bool using (Bool; not; _∧_; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Integer as ℤ using (+_)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; _/_)

open import Slides.Diagram.NatQ using (ι)

import Slides.Anim.Track as Tr
open import Slides.Time using (module Sem)
open import Slides.Time.Rat using (ratClock)
open import Slides.Anim.Syntax using (Anim)
open import Slides.Anim.Sample using (frames; TM)
open import Slides.Diagram.Draw using (Layout)
open import Slides.Diagram.Ordered using (_<ᵇℚ_)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Slides.Diagram.Scalar using (ratOps)
open import Slides.Diagram.Syntax using (Dia)

------------------------------------------------------------------------
-- Real time on a track

-- how far through `d` ticks the time `τ` is (clamped above; a negative time never reaches a
-- piece, see `Slides.Anim.Sample.holdT`)
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
-- Animations in real time

-- the parameter a track gives at real time `τ`
ratVal : Tr.Track ℚ → ℚ → ℚ
ratVal tr = proj₂ (sampleAt Tr.ℚLerp tr)

-- what is shown when, in ℚ
framesQ : Anim → TM ratClock (Dia ℚ)
framesQ = frames ratClock ratVal

-- The frame at real time `τ`: the layout, in ℚ, of the diagram running at `τ`
-- (`nothing` when none is).
frameAt : Anim → ℚ → Maybe (Layout ℚ)
frameAt a τ = Maybe.map (LayoutWith.layout ratOps) (proj₂ (framesQ a) τ)
