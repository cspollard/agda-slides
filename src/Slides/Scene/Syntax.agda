{-# OPTIONS --safe --without-K #-}

-- A scene is a term of the temporal signature (after Hudak's temporal media): the free monad
-- over it, so substituting scenes for leaves is bind.
--
--   Par a b     overlay, absence is the unit      Hold d a    present on [0, d) of its own time
--   Seq a b     b after a                          Delay d a   its time 0 is at d
--   Repeat n a  n copies end to end                Drive c a   leaves below read `c` at local time
--
--   time   0    1    2    3    4    5
--   a      [a a a)                          Hold 3 a
--   b                [b b b b)              Delay 3 (Hold 4 b)
--   Seq (Hold 3 a) (Hold 4 b) = Par (Hold 3 a) (Delay 3 (Hold 4 b));  at tick 4 the sample reads b at its local time 1
--
-- `T` is the scalar of durations, `D` the type of drivers (terms of the Coupling theory).
-- A leaf under no window is present from 0 for ever.  Meaning: `Slides.Scene.Events`.

module Slides.Scene.Syntax where

open import Level using (0ℓ)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤)
open import Data.Container.Core using (Container; _▷_; _⇒_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Data.Product.Base using (_,_)
open import Container.Pick using (pick2)
open import Container.Lowering using (translate)

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

-- Change of clock and drivers: a container morphism (same arities), so scenes map by `translate`

mapOp : ∀ {T₁ T₂ D₁ D₂} → (T₁ → T₂) → (D₁ → D₂) → Op T₁ D₁ → Op T₂ D₂
mapOp h g Seq        = Seq
mapOp h g Par        = Par
mapOp h g (Hold d)   = Hold (h d)
mapOp h g (Delay d)  = Delay (h d)
mapOp h g (Repeat n) = Repeat n
mapOp h g (Drive c)  = Drive (g c)

mapSC : ∀ {T₁ T₂ D₁ D₂} → (T₁ → T₂) → (D₁ → D₂) → SceneC T₁ D₁ ⇒ SceneC T₂ D₂
mapSC h g = record { shape = mapOp h g ; position = pos }
  where
    pos : ∀ {o} → arity (mapOp h g o) → arity o
    pos {Seq}      p = p
    pos {Par}      p = p
    pos {Hold _}   p = p
    pos {Delay _}  p = p
    pos {Repeat _} p = p
    pos {Drive _}  p = p

mapScene : ∀ {T₁ T₂ D₁ D₂ A} → (T₁ → T₂) → (D₁ → D₂) → Scene T₁ D₁ A → Scene T₂ D₂ A
mapScene h g = translate (mapSC h g)
