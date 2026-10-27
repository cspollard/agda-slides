{-# OPTIONS --safe --without-K #-}

-- THEORY MODULE (spike): no executable imports it.
--
-- The existing theorem, for the existing `frameAt`, on template-only animations: the sum of
-- `Assembly` (the assembly on the Stage 2 container) and `OldNew` (the container's frames are
-- `animAt`'s at whole ticks).

module Slides.Spike.Stage2.Old where

open import Data.Bool using (true)
open import Data.Maybe using (Maybe; just)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; _<ᵇ_)
open import Data.Product using (_×_; _,_; proj₂; ∃)
open import Data.Rational using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Slides.Diagram.Draw using (mapLayout)
open import Slides.Diagram.NatQ using (ι)
open import Slides.Diagram.Scalar using (natOps; ratOps)
open import Slides.Anim.Nth using (nth)
import Slides.Anim.Syntax as A
open import Slides.Anim.Timeline using (timeline; frames)
open import Slides.Diagram.Syntax using (atop)
open import Slides.Anim.Continuous using (frameAt)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Slides.Spike.Stage2.Scene
open import Slides.Spike.Stage2.OldNew
open import Slides.Spike.Stage2.Assembly

frameAt-toAnim : ∀ t τ → frameAt (toAnim t) τ ≡ Maybe.map (LayoutWith.layout ratOps) (proj₂ (animT t) τ)
frameAt-toAnim t τ rewrite animAt-toAnim t = refl

-- `frameAt-assembly-all` of `Slides.Anim.Assembly.Continuous`, re-derived
frameAt-assembly-new :
  ∀ t → AllExactT t → ∀ k → (k <ᵇ A.dur (toAnim t)) ≡ true →
  ∃ λ F → nth (timeline atop (frames natOps) (toAnim t)) k ≡ just F
        × frameAt (toAnim t) (ι k) ≡ just (mapLayout ι (LayoutWith.layout natOps F))
frameAt-assembly-new t ex k hk with frameAt-assembly′ t ex k hk
... | F , eF , e = F , eF , trans (frameAt-toAnim t (ι k)) (trans (cong (Maybe.map (LayoutWith.layout ratOps)) (sym (embed-agree t k))) e)
