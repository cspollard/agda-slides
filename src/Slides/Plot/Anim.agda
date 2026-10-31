{-# OPTIONS --safe --without-K #-}

-- Animated plots.  A plot is a pure value, so an animation is a list of plots drawn as frames
-- (`Slides.Deck.Anim.frames`): nothing in `Dia` has to move.
--
--   reveal    the series one at a time: the plot with the first k series, k = 1 … n, one act each
--             (a reveal step per click in `animate`)
--   morph     a flip book from one plot to another of the same shape: every number is
--             `a + t (b − a)` at the eased progress t (`lerpPlot`); the axis range moves too, so
--             ticks and labels follow it
--
-- The pieces that are not points (style, legend, labels) are the first plot's, and lists are
-- matched position by position (the shorter wins), so a morph is between datasets of one shape.
-- A morph is a frame list, as an animated axis range cannot be one scalar term (no multiplication
-- in `Space`); the endpoints are the plots themselves (`lerp-0`, `lerp-1`).

module Slides.Plot.Anim where

open import Data.List using (List; []; _∷_; map; zipWith; upTo; take)
open import Data.Nat as ℕ using (ℕ; suc)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)

open import Slides.Deck.Anim using (Anim; frame′; liftDia; frames; flipTween; Easing)
open import Slides.Plot.Mark
open import Slides.Plot.Render using (Plot; AxisSpec; render)

-- along the segment from a to b
lerp : ℚ → ℚ → ℚ → ℚ
lerp t a b = a + t * (b - a)

lerp-0 : ∀ a b → lerp 0ℚ a b ≡ a
lerp-0 a b = trans (cong (a +_) (ℚP.*-zeroˡ (b - a))) (ℚP.+-identityʳ a)

lerp-1 : ∀ a b → lerp 1ℚ a b ≡ b
lerp-1 a b = trans (cong (a +_) (ℚP.*-identityˡ (b - a)))
            (trans (ℚP.+-comm a (b - a))
            (trans (ℚP.+-assoc b (ℚ.- a) a)
            (trans (cong (b +_) (ℚP.+-inverseˡ a)) (ℚP.+-identityʳ b))))

-- a point that does not move
lerp-same : ∀ t a → lerp t a a ≡ a
lerp-same t a = trans (cong (λ z → a + t * z) (ℚP.+-inverseʳ a)) (trans (cong (a +_) (ℚP.*-zeroʳ t)) (ℚP.+-identityʳ a))

lerpMark : ℚ → Mark ℚ ℚ → Mark ℚ ℚ → Mark ℚ ℚ
lerpMark t = zipWith⁺ (lerp t) (lerp t)

lerpPlot : ℚ → Plot → Plot → Plot
lerpPlot t a b = record a
  { xaxis   = axis (Plot.xaxis a) (Plot.xaxis b)
  ; yaxis   = axis (Plot.yaxis a) (Plot.yaxis b)
  ; content = zipWith (λ x y → record x { mark = lerpMark t (Series.mark x) (Series.mark y) }) (Plot.content a) (Plot.content b) }
  where axis : AxisSpec → AxisSpec → AxisSpec
        axis u v = record u { lo = lerp t (AxisSpec.lo u) (AxisSpec.lo v) ; hi = lerp t (AxisSpec.hi u) (AxisSpec.hi v) }

-- the series one at a time: one act (a reveal step) for each prefix of the content
reveal : Plot → List Anim
reveal p = map (λ k → frame′ 1 (liftDia (render (record p { content = take k (Plot.content p) }))))
               (map suc (upTo (length (Plot.content p))))
  where open import Data.List using (length)

-- a flip book from `a` to `b` in `n` frames, eased
morph : ℕ → Easing → Plot → Plot → Anim
morph n e a b = flipTween n e (λ t → render (lerpPlot t a b))
