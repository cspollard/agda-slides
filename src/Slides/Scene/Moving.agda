{-# OPTIONS --safe --without-K #-}

-- Moving values: a driver is a term of the Coupling theory, not a track datatype.
--
-- `move e a b d` is `lerp (ease e (ratio now d)) a b`: the value going from `a` to `b` over `d`
-- along the easing `e`.  A segment is `tween`: `hold d (drive (move e a b d) leaf)`.
--
--   move-end   at local time `d` the value is `b` (the Coupling theory's own law)
--
-- ℕ has no ratios, so there is no ℕ instance; the tick clock reads these scenes at `ι`
-- (`Slides.Scene.Tick`).  Re-exports `Slides.Scene.Animation` at these drivers.

open import Slides.Scalar.Core using (Sub)
open import Slides.Scalar.Space using (Space; Scale)
open import Slides.Scalar.Time using (Time)
open import Slides.Scalar.Coupling

module Slides.Scene.Moving {T : Set} (Sp : Space T) (Tm : Time T)
       {Sb : Sub (Time.ord Tm)} {Scl : Scale (Time.ord Tm) T} (C : Coupling Tm Sb Scl) where

open import Data.Fin using (zero; suc)
open import Data.Product.Base using (_,_)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Relation.Nullary using (¬_)

open import Container.Interpret.Plain using (pfold)
open import Container.Pick using (pick2)
open import Slides.Scene.Syntax
open Time Tm using (0#; _≤_)
open Coupling C using (lerp; progress)

Drv : Set
Drv = CouplingC ⋆ Maybe T

evalDrv : Drv → T → T
evalDrv c τ = pfold CouplingC (couplingH C) (maybe (λ k → k) τ) c

open import Slides.Scene.Animation Sp Tm evalDrv public

-- the value moving from `a` to `b` over `d`
move : Easing → T → T → T → Drv
move e a b d = impure (Lerp , λ { zero → impure (Ease e , λ _ → impure (Ratio , pick2 (pure nothing) (pure (just d))))
                                 ; (suc zero) → pure (just a)
                                 ; (suc (suc zero)) → pure (just b) })

move-val : ∀ e a b d τ → evalDrv (move e a b d) τ ≡ lerp (progress e τ d) a b
move-val e a b d τ = refl

-- it ends at `b`
move-end : ∀ e {a b} d → a ≤ b → ¬ (d ≡ 0#) → evalDrv (move e a b d) d ≡ b
move-end e d a≤b d≢0 = trans (move-val e _ _ d d) (Coupling.move-end C e d a≤b d≢0)

-- a leaf held for `d`, its parameter moving from `a` to `b`
tween : Easing → T → T → T → Leaf → Anim
tween e a b d l = hold d (drive (move e a b d) (pure l))
