{-# OPTIONS --safe --without-K #-}

-- Containers and lowerings form a category.
--
-- Objects are containers, arrows are lowerings (Kleisli arrows of the free
-- monad, `Container.Lowering`), with `ret` as identity and equality of the
-- lowered programs as the equality of arrows.  Interpreting a deck is then
-- a functor out of this category (`lower-fusion` is its action on arrows).

module Container.Lowering.Category where

open import Level using (0ℓ; suc)
open import Data.Container.Core using (Container)
open import Relation.Binary.Structures using (IsEquivalence)

open import Categories.Category.Core using (Category)

open import Container.Lowering

Lowerings : Category (suc 0ℓ) 0ℓ 0ℓ
Lowerings = record
  { Obj       = Container 0ℓ 0ℓ
  ; _⇒_       = Lowering
  ; _≈_       = _≈ˡ_
  ; id        = ret
  ; _∘_       = λ m l → l ⋙ m
  ; assoc     = λ {_} {_} {_} {_} {f} {g} {h} a → lower-⋙ g h (f a)
  ; sym-assoc = λ {_} {_} {_} {_} {f} {g} {h} a → sym≈ (lower-⋙ g h (f a))
  ; identityˡ = λ {_} {_} {f} a → lower-ret (f a)
  ; identityʳ = λ {_} {_} {f} a → bind-pure≈ (f a)
  ; identity² = λ a → lower-ret (ret a)
  ; equiv     = record
      { refl  = λ a → refl≈ _
      ; sym   = λ e a → sym≈ (e a)
      ; trans = λ e e′ a → trans≈ (e a) (e′ a)
      }
  ; ∘-resp-≈  = λ {_} {_} {_} {_} {_} {_} {i} f≈h g≈i a → lower-cong f≈h (g≈i a)
  }
