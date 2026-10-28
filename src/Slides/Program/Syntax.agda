{-# OPTIONS --safe --without-K #-}

-- Programs: scenes that can wait for a command.
--
-- The signature of a program is the scene signature plus one operation, `await c`, with a
-- single continuation: "wait until the command `c` arrives, then go on".  A program is the free
-- monad over the sum (`Container.Sum`), so a scene is a program that never waits (`inject`),
-- substitution is bind, and the meaning is a fold (`Slides.Program.Machine`).
--
--   inject s   a scene as a program (the container morphism `inl`)
--   skip p     a program as a scene: every wait is taken as already satisfied (a lowering)
--
-- `skip-inject`: skip is a retraction of inject; `skip-bind`: skip is a monad morphism.

module Slides.Program.Syntax where

open import Level using (0ℓ; lift)
open import Data.Unit using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Data.Container.Core using (Container; _▷_)
open import Data.Container.Combinator using (_⊎_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Container.Lowering using (Lowering; lower; translate)
open import Container.Lowering.Properties using (_≈⋆_; refl≈; lower-bind)
open import Container.Sum using (inl)
open import Slides.Scene.Syntax using (SceneC; Scene)

-- the commands a program may wait for: the set `C`
AwaitC : Set → Container 0ℓ 0ℓ
AwaitC C = C ▷ λ _ → ⊤

ProgC : Set → Set → Set → Container 0ℓ 0ℓ
ProgC T D C = SceneC T D ⊎ AwaitC C

Program : Set → Set → Set → Set → Set
Program T D C A = ProgC T D C ⋆ A

module _ {T D C : Set} where

  await : C → Program T D C ⊤
  await c = impure (inj₂ c , λ _ → pure tt)

  inject : ∀ {A} → Scene T D A → Program T D C A
  inject = translate inl

  skipOp : Lowering (ProgC T D C) (SceneC T D)
  skipOp (inj₁ o) = impure (o , pure)
  skipOp (inj₂ _) = pure tt

  skip : ∀ {A} → Program T D C A → Scene T D A
  skip = lower skipOp

  skip-inject : ∀ {A} (s : Scene T D A) → skip (inject {A = A} s) ≈⋆ s
  skip-inject (pure _)         = lift refl
  skip-inject (impure (o , k)) = refl , λ q → skip-inject (k q)

  skip-bind : ∀ {A B} (p : Program T D C A) (f : A → Program T D C B) →
              skip (p >>= f) ≈⋆ (skip p >>= λ a → skip (f a))
  skip-bind = lower-bind skipOp
