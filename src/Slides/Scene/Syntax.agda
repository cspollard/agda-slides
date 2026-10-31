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
open import Data.Unit using (⊤; tt)
open import Data.Container.Core using (Container; _⇒_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Data.Product.Base using (Σ; _,_)
open import Container.Pick using (pick2)
open import Container.Lowering using (translate)
open import Container.Tagged using (Tagged; over)

-- A command is a tag and a payload; the arity of a tag does not depend on the scalars.

data Tag : Set where
  seqK parK holdK delayK repeatK driveK : Tag

arity : Tag → Set
arity seqK    = Fin 2
arity parK    = Fin 2
arity holdK   = ⊤
arity delayK  = ⊤
arity repeatK = ⊤
arity driveK  = ⊤

-- the scalars a tag holds: a duration (`T`) or a driver (`D`)
Held : Tag → Set → Set → Set
Held holdK   T D = T
Held delayK  T D = T
Held repeatK T D = ℕ
Held driveK  T D = D
Held seqK    T D = ⊤
Held parK    T D = ⊤

Op : Set → Set → Set
Op T D = Σ Tag (λ t → Held t T D)

pattern Seq        = seqK , tt
pattern Par        = parK , tt
pattern Hold d     = holdK , d
pattern Delay d    = delayK , d
pattern Repeat n   = repeatK , n
pattern Drive c    = driveK , c

SceneC : Set → Set → Container 0ℓ 0ℓ
SceneC T D = Tagged arity (λ t → Held t T D)

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

-- Change of clock and drivers: a container morphism with the identity on positions, so scenes map by `translate`

mapP : ∀ {T₁ T₂ D₁ D₂} → (T₁ → T₂) → (D₁ → D₂) → ∀ t → Held t T₁ D₁ → Held t T₂ D₂
mapP h g seqK    _ = tt
mapP h g parK    _ = tt
mapP h g holdK   d = h d
mapP h g delayK  d = h d
mapP h g repeatK n = n
mapP h g driveK  c = g c

mapOp : ∀ {T₁ T₂ D₁ D₂} → (T₁ → T₂) → (D₁ → D₂) → Op T₁ D₁ → Op T₂ D₂
mapOp h g (t , p) = t , mapP h g t p

mapSC : ∀ {T₁ T₂ D₁ D₂} → (T₁ → T₂) → (D₁ → D₂) → SceneC T₁ D₁ ⇒ SceneC T₂ D₂
mapSC h g = over arity (mapP h g)

mapScene : ∀ {T₁ T₂ D₁ D₂ A} → (T₁ → T₂) → (D₁ → D₂) → Scene T₁ D₁ A → Scene T₂ D₂ A
mapScene h g = translate (mapSC h g)
