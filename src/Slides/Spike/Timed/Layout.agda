{-# OPTIONS --safe --without-K #-}

-- THEORY MODULE (spike): the lifting lemma at the layout algebra over ℚ, and the negative
-- result for absence.

module Slides.Spike.Timed.Layout where

open import Data.Fin using (zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Slides.Diagram.NatQ using (ι)
open import Slides.Diagram.Draw using (Layout)
open import Slides.Diagram.Scalar using (ratOps)
open import Slides.Diagram.Syntax
open import Slides.Diagram.Layout using (module LayoutWith)
import Slides.Diagram.Place ratOps as P
open import Data.Sum using (inj₁)
open import Data.Container.FreeMonad using (impure)
open import Slides.Anim.Timeline using (mergeM)
open import Slides.Spike.Timed
open import Slides.Spike.Timed.Properties

open LayoutWith ratOps using (layoutAlgebra; layout)

-- the layout algebra is extensional (pointwise-congruent in its children); without funext
-- this is what the setoid `Func.cong` of `Container.Sum.copair` provides
layout-ext : ∀ o {x y : arity o → Layout ℚ} → (∀ i → x i ≡ y i) → layoutAlgebra o x ≡ layoutAlgebra o y
layout-ext (Rectangle _ _ _)   p = refl
layout-ext (Disc _ _)          p = refl
layout-ext (Segment _ _ _)     p = refl
layout-ext (Text _ _ _ _)      p = refl
layout-ext (Spacer _ _)        p = refl
layout-ext (Beside al)         p = cong₂ (P.besideA al) (p zero) (p (suc zero))
layout-ext (Above al)          p = cong₂ (P.aboveA al) (p zero) (p (suc zero))
layout-ext Atop                p = cong₂ P.atop (p zero) (p (suc zero))
layout-ext LabelAbove          p = cong₂ P.labelAbove (p zero) (p (suc zero))
layout-ext LabelBelow          p = cong₂ P.labelBelow (p zero) (p (suc zero))
layout-ext (Place w h x y)     p = cong (P.place w h x y) (p tt)
layout-ext (Overlay w h)       p = cong₂ (P.overlay w h) (p zero) (p (suc zero))
layout-ext (Named n)           p = cong (P.named n) (p tt)
layout-ext (Connect a pa b pb s) p = cong (P.connectP a pa b pb s) (p tt)

-- INSTANCE: the layout of a scene sampled at τ is the layout of the diagram it shows at τ
layout-at : (t : Scene ℚ) (τ : ℚ) →
  proj₂ (sample layoutAlgebra t) τ ≡ Maybe.map layout (restrict t τ)
layout-at = lifting-lemma-at layoutAlgebra layout-ext

layout-dur : (t : Scene ℚ) → proj₁ (sample layoutAlgebra t) ≡ proj₁ (sample con t)
layout-dur = lifting-lemma-dur layoutAlgebra layout-ext

-- Par of layouts is `P.atop` of layouts, by definition (this is `Slides.Anim.Timeline.merge`
-- at `F = Layout ℚ`, the shape that `frameAt-assembly` states)
par-is-atop : ∀ (a b : Scene ℚ) τ →
  proj₂ (sample layoutAlgebra (impure (inj₁ Par , fin2 a b))) τ ≡
  mergeM P.atop (proj₂ (sample layoutAlgebra a) τ) (proj₂ (sample layoutAlgebra b) τ)
par-is-atop a b τ = refl

-- ABSENCE: erasing an absent child (the lenient reading, "absence is the unit") is NOT lawful
-- for `Overlay`: the frame size is declared, so there is no layout `e` with
-- `overlay w h e d ≡ d`, whatever `e` is.
overlay-no-unit : ∀ e → ¬ (P.overlay (ι 4) (ι 4) e (P.spacer 1ℚ 1ℚ) ≡ P.spacer 1ℚ 1ℚ)
overlay-no-unit e eq with cong Layout.width eq
... | ()
