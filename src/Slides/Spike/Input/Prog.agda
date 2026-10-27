{-# OPTIONS --safe --without-K #-}

-- Spike (plan/Unify.md, Stage 0, input): programs parametric in the commands
-- they await.
--
--   SceneC V  = V ▷ ⊤        show a piece of scene `v` (stand-in for the scene container)
--   AwaitC C  = C ▷ ⊤        `await c`: one continuation, taken when `c` arrives
--   ParC      = ⊤ ▷ Bool     two parallel continuations
--   Prog V C A = (SceneC V ⊎ AwaitC C ⊎ ParC) ⋆ A
--
-- `AwaitC` is covariant in the command type: a map `C → D` of commands is a
-- container morphism `AwaitC C ⇒ AwaitC D` (`mapC`), so programs are lifted
-- into a larger vocabulary by `Container.Lowering.translate`, and `_‖_` is
-- total at `C₁ ⊎ C₂`.  A choice with one child per command would NOT be
-- covariant (`no-OnC-inl`): see the negative lemma at the end.

module Slides.Spike.Input.Prog (V : Set) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_)
open import Data.String.Base using (String)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit.Base using (⊤; tt)
open import Data.Container.Core using (Container; _▷_; _⇒_; Shape; Position)
open import Data.Container.Combinator using () renaming (_⊎_ to _⊎C_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
import Data.Container.Core as CC

open import Container.Lowering using (translate)

SceneC : Container _ _
SceneC = V ▷ λ _ → ⊤

AwaitC : Set → Container _ _
AwaitC C = C ▷ λ _ → ⊤

ParC : Container _ _
ParC = ⊤ ▷ λ _ → Bool

ProgC : Set → Container _ _
ProgC C = SceneC ⊎C (AwaitC C ⊎C ParC)

Prog : Set → Set → Set
Prog C A = ProgC C ⋆ A

------------------------------------------------------------------------
-- Smart constructors

show : ∀ {C} → V → Prog C ⊤
show v = impure (inj₁ v , λ _ → pure tt)

await : ∀ {C} → C → Prog C ⊤
await c = impure (inj₂ (inj₁ c) , λ _ → pure tt)

infixr 5 _⨾_
_⨾_ : ∀ {C A B} → Prog C A → Prog C B → Prog C B
p ⨾ q = p >>= λ _ → q

------------------------------------------------------------------------
-- Changing the command vocabulary is a container morphism

mapC : ∀ {C D} → (C → D) → ProgC C ⇒ ProgC D
CC._⇒_.shape (mapC f) (inj₁ v)         = inj₁ v
CC._⇒_.shape (mapC f) (inj₂ (inj₁ c))  = inj₂ (inj₁ (f c))
CC._⇒_.shape (mapC f) (inj₂ (inj₂ s))  = inj₂ (inj₂ s)
CC._⇒_.position (mapC f) {inj₁ _}         p = p
CC._⇒_.position (mapC f) {inj₂ (inj₁ _)}  p = p
CC._⇒_.position (mapC f) {inj₂ (inj₂ _)}  p = p

mapP : ∀ {C D A} → (C → D) → Prog C A → Prog D A
mapP f = translate (mapC f)

-- Parallel composition at the sum of the vocabularies: each side is lifted
-- along its own injection, so it can only ever await its own commands.
infixr 4 _‖_
_‖_ : ∀ {C₁ C₂ A} → Prog C₁ A → Prog C₂ A → Prog (C₁ ⊎ C₂) A
p ‖ q = impure (inj₂ (inj₂ tt) , λ { true → mapP inj₁ p ; false → mapP inj₂ q })

------------------------------------------------------------------------
-- Navigation: the standard vocabulary every deck requires

data Nav : Set where
  next prev first last : Nav
  goto      : ℕ → Nav
  gotoLabel : String → Nav

-- A deck awaits the navigation vocabulary plus extra commands.
Deck : Set → Set → Set
Deck C A = Prog (Nav ⊎ C) A

-- `pause` is `await next`.
pause : ∀ {C} → Deck C ⊤
pause = await (inj₁ next)

------------------------------------------------------------------------
-- Choice with one child per command is not covariant in the commands

OnC : Set → Container _ _
OnC C = ⊤ ▷ λ _ → C

-- There is no container morphism `OnC ⊥ ⇒ OnC (⊥ ⊎ ⊤)` (it would have to
-- turn the command `inj₂ tt` into a command of `⊥`), so a program built with
-- `OnC` cannot be lifted along `inl`: offered commands must be part of the shape.
no-OnC-inl : OnC ⊥ ⇒ OnC (⊥ ⊎ ⊤) → ⊥
no-OnC-inl m = CC._⇒_.position m {tt} (inj₂ tt)
