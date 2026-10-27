{-# OPTIONS --safe --without-K #-}

-- Lowerings: Kleisli maps between containers.
--
-- A container morphism `C ⇒ D` sends each command of `C` to one command of
-- `D`.  A *lowering* sends each command of `C` to a whole *program* over
-- `D` that returns the command's result: it is a natural transformation
-- `⟦C⟧ ⇒ D ⋆` (equivalently a Kleisli arrow for the free monad of `D`),
-- and the vocabulary can shrink or grow along it.  A deck is lowered by
-- extending the lowering to programs (`lower`, the Kleisli extension).
--
-- * Lowerings compose (`_⋙_`) with the identity `ret`; the laws hold up to
--   equality of programs (`_≈⋆_`, `Container.FreeMonad.Eq` at the
--   propositional setoid), so containers and lowerings form a category
--   (`Container.Lowering.Category`).
-- * Container morphisms are the lowerings of one command to one command
--   (`embed`).
-- * `lower` is a monad morphism (`lower-bind`).
-- * Fusion: interpreting a lowered program equals interpreting the
--   original with the algebra pulled back along the lowering
--   (`lower-fusion`); this generalises `Container.Interpret.fusion`.

module Container.Lowering where

open import Level using (Level; _⊔_)
open import Data.Product.Base using (_,_)
open import Data.Container.Core using (Container; Shape; Position; _⇒_; shape; position)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)

open import Container.Polynomial
open import Container.FreeMonad
open import Container.FreeMonad.Algebraic

private
  variable
    s p c a b d : Level

------------------------------------------------------------------------
-- Lowerings

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
