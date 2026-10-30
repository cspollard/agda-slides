{-# OPTIONS --safe --without-K #-}

-- Lowerings: Kleisli maps between containers.
--
--   Lowering C D = (a : Shape C) → D ⋆ Position C a      each command of C becomes a program over D
--
-- A container morphism is the special case of one command to one command (`embed`).
-- `lower` is the Kleisli extension to whole programs, `_⋙_` composes (first `l`, then `m`),
-- `ret` is the identity.  Laws, up to equality of programs `_≈⋆_`, are in
-- `Container.Lowering.Properties`; they make containers and lowerings a category
-- (`Container.Lowering.Category`).

module Container.Lowering where

open import Level using (Level; _⊔_)
open import Data.Product.Base using (_,_)
open import Data.Container.Core using (Container; Shape; Position; _⇒_; shape; position)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)

open import Relation.Binary.PropositionalEquality using (setoid)

open import Container.Polynomial
open import Container.FreeMonad
open import Container.FreeMonad.Algebraic

private
  variable
    s p c a b d : Level

-- Equality of programs: equal shapes, pointwise equal continuations, equal leaves

infix 4 _≈⋆_

_≈⋆_ : ∀ {C : Container s p} {X : Set c} → C ⋆ X → C ⋆ X → Set (c ⊔ s ⊔ p)
_≈⋆_ {C = C} {X = X} = Eq {C = C} (setoid X)


Lowering : Container s p → Container s p → Set (s ⊔ p)
Lowering C D = (a : Shape C) → D ⋆ Position C a

-- The identity lowering.
ret : ∀ {C : Container s p} → Lowering C C
ret a = impure (a , pure)

-- A container morphism is a lowering of each command to one command.
embed : ∀ {C D : Container s p} → C ⇒ D → Lowering C D
embed m a = impure (shape m a , λ q → pure (position m q))

-- The Kleisli extension: lower every command of a program.
lower : ∀ {C D : Container s p} {X : Set c} → Lowering C D → C ⋆ X → D ⋆ X
lower l (pure x)          = pure x
lower l (impure (a , k)) = l a >>= λ q → lower l (k q)

-- Composition, diagrammatically: first `l`, then `m`.
infixr 9 _⋙_

_⋙_ : ∀ {C D E : Container s p} → Lowering C D → Lowering D E → Lowering C E
(l ⋙ m) a = lower m (l a)

-- Lowering along `embed m` is translation along `m` (the program
-- transformation of `Container.Interpret.Translate`).
translate : ∀ {C D : Container s p} {X : Set c} → C ⇒ D → C ⋆ X → D ⋆ X
translate m (pure x)         = pure x
translate m (impure (a , k)) =
  impure (shape m a , λ q → translate m (k (position m q)))
