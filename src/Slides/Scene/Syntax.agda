{-# OPTIONS --safe --without-K #-}

-- The temporal signature and scenes: temporal media after Hudak, as a free monad.
--
--   Seq a b     b after a (a window of the length of each)
--   Par a b     together, overlaid; absence is the unit
--   Hold d a    present on [0, d) of its own time (the relative presence window)
--   Delay d a   its time 0 is at d (the shift)
--   Repeat n a  n copies end to end
--   Drive c a   the leaves below read the value of the driver `c` at their local time
--
-- `T` is the scalar of durations and `D` the type of drivers: a driver is a term of the Coupling
-- theory (`Slides.Scene.Animation`), so a moving value is not a separate datatype.  A leaf
-- under no window is present from time 0 for ever; `Hold` gives it a window.  `Scene T D A` is
-- the free monad over the signature, so substituting scenes for leaves is bind (nesting by
-- substitution, `Slides.Scene.Sample.sample-bind`).  Meaning: `Slides.Scene.Events`.

module Slides.Scene.Syntax where

open import Level using (0ℓ)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤)
open import Data.Container.Core using (Container; _▷_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Data.Product.Base using (_,_)
open import Container.Pick using (pick2)

data Op (T D : Set) : Set where
  Seq Par     : Op T D
  Hold Delay  : T → Op T D
  Repeat      : ℕ → Op T D
  Drive       : D → Op T D

arity : ∀ {T D} → Op T D → Set
arity Seq        = Fin 2
arity Par        = Fin 2
arity (Hold _)   = ⊤
arity (Delay _)  = ⊤
arity (Repeat _) = ⊤
arity (Drive _)  = ⊤

SceneC : Set → Set → Container 0ℓ 0ℓ
SceneC T D = Op T D ▷ arity

Scene : Set → Set → Set → Set
Scene T D A = SceneC T D ⋆ A

module _ {T D A : Set} where
  infixr 6 _⨾_
  infixr 7 _∥_

  _⨾_ _∥_ : Scene T D A → Scene T D A → Scene T D A
  a ⨾ b = impure (Seq , pick2 a b)
  a ∥ b = impure (Par , pick2 a b)

  hold delay : T → Scene T D A → Scene T D A
  hold d a  = impure (Hold d , λ _ → a)
  delay d a = impure (Delay d , λ _ → a)

  repeat : ℕ → Scene T D A → Scene T D A
  repeat n a = impure (Repeat n , λ _ → a)

  drive : D → Scene T D A → Scene T D A
  drive c a = impure (Drive c , λ _ → a)
