{-# OPTIONS --safe --without-K #-}

-- Animation: a scene of diagrams whose scalars are terms in one time parameter, read at a tick.
--
-- The parameter (`nothing`; `just k` a constant) is the driver's value at the leaf's local time
-- (0 outside any `Drive`).  Frames overlay in the join of their frames (`ovl`, associative;
-- absence is the unit).
--
--   frame s n       the frame at tick `n`, the reading at `tick n`
--   frame-assembly  it is the overlay of the layouts of the leaves active at `n`, each at its
--                   local time (from `Slides.Scene.Laws`)

open import Slides.Scalar.Space using (Space)
open import Slides.Scalar.Time using (Time)

module Slides.Scene.Animation {T : Set} (Sp : Space T) (Tm : Time T) {D : Set} (val : D → T → T) where

open import Data.List using (List; []; _∷_; _++_; map)
import Data.List.Properties as ListP
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Nat using (ℕ)
open import Data.Product.Base using (proj₂)
open import Data.Container.FreeMonad using (_⋆_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Container.Interpret.Plain using (Handler; pfold)
open import Slides.Scalar.Core using (_⊕_)
open import Slides.Scalar.Space using (spaceH)
open import Slides.Scalar.Time using (timeH)
open import Slides.Scalar.Hom using (ScC)
open import Slides.Diagram.Draw using (Layout; mkLayout)
open import Slides.Diagram.Syntax using (Dia; mapDia)
import Slides.Diagram.Place Sp as P
open import Slides.Diagram.Laws Sp using (ovl; layoutOverlay) public
open import Slides.Diagram.Layout Sp using (layout)
open import Slides.Scene.Syntax
open Space Sp using (_⊔_; _-_)

-- Frames overlay

open import Slides.Scene.Events {T} {D} (Space.ord Sp) (Space.sub Sp) public
open import Slides.Scene.Sample {T} {D} {Layout T} (Space.ord Sp) (Space.sub Sp) val layoutOverlay public
open import Slides.Scene.Laws {T} {D} {Layout T} (Space.ord Sp) (Space.sub Sp) val layoutOverlay
  using (actives; leafAt; overlay; sample-assembly)

-- Leaves: diagrams over scalar terms in the parameter

Sc : Set
Sc = ScC ⋆ Maybe T

Leaf : Set
Leaf = Dia Sc

scH : Handler ScC T
scH = spaceH Sp ⊕ timeH Tm

-- the scalar at the parameter `p`
evalSc : T → Sc → T
evalSc p = pfold ScC scH (maybe (λ k → k) p)

inst : T → Leaf → Dia T
inst p = mapDia (evalSc p)

leafLayout : Leaf → T → Layout T
leafLayout l p = layout (inst p l)

Anim : Set
Anim = Scene T D Leaf

-- Frames

frameAt : Anim → T → Maybe (Layout T)
frameAt s t = proj₂ (sample leafLayout s) t nothing

-- the frame at the whole tick `n`
frame : Anim → ℕ → Maybe (Layout T)
frame s n = frameAt s (Time.tick Tm n)

-- The assembly: the frame is the overlay of the layouts of the leaves active at that tick.
frame-assembly : ∀ s n →
  frame s n ≡ overlay (map (λ e → leafAt leafLayout e (Time.tick Tm n) nothing)
                           (actives (events s) (Time.tick Tm n)))
frame-assembly s n = sample-assembly leafLayout s (Time.tick Tm n) nothing

-- each active leaf is laid out at its own instance
leaf-instance : ∀ (e : Event Leaf) t →
                leafAt leafLayout e t nothing ≡ layout (inst (param (orElse (driver e) nothing) (t - onset e)) (leaf e))
leaf-instance e t = refl
