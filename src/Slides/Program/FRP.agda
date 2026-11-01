{-# OPTIONS --safe --without-K #-}

-- Programs as FRP: the switcher for the scene's time.
--
-- A program means `Beh C Timed` (`Slides.Program.Sem`); a `Timed` output is read at local time with
-- no driver (`readAt`, a map of setoids since equal readings read equal).  `Semantics.FRP.switch`
-- of that reader turns a program's behaviour into a function of a timed command stream and the
-- instant: `(program ⟨$⟩ b) es t` is the scene reading at `t − t_last`, the commands seen being those
-- at or before `t`.  The laws are those of `Semantics.FRP`, causality included.

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Slides.Scalar.Core using (OrdMon; Sub)
open import Slides.Diagram.Overlay using (Overlays)

module Slides.Program.FRP {T D X : Set} (M : OrdMon T) (Sb : Sub M) (val : D → T → T) (O : Overlays X)
       (C : Set) where

open import Data.Maybe using (Maybe; nothing)
open import Data.Product.Base using (proj₂)
open import Function.Bundles using (Func; _⟨$⟩_)
import Relation.Binary.PropositionalEquality.Properties as ≡P

open import Semantics.Behaviour using (Beh; _⇉_)
import Slides.Scene.Equiv {T} {D} {X} M Sb val O as E
open import Slides.Scene.Sample {T} {D} {X} M Sb val O using (Timed)

-- the reading of a scene at local time, nothing driving it
readAt : Func E.TimedS (T ⇉ ≡P.setoid (Maybe X))
readAt = record { to = λ o u → proj₂ o u nothing ; cong = λ e u → proj₂ e u nothing }

open import Semantics.FRP M Sb C (≡P.setoid (Maybe X)) public



program : Func (Beh C E.TimedS) (Event ⇉ Behaviour)
program = switch readAt
