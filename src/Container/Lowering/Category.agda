{-# OPTIONS --safe --without-K #-}

-- THEORY MODULE: proofs and the vocabulary they need; no executable imports it (`tests/check_closure.py`).
--
-- `Lowerings`: containers as objects, lowerings as arrows (Kleisli arrows of the free monad),
-- `ret` as identity, equality of the lowered programs as equality of arrows.
-- Interpreting is a functor out of it (`lower-fusion` is its action on arrows).

module Container.Lowering.Category where

open import Level using (0ℓ; suc)
open import Data.Container.Core using (Container)
open import Categories.Category.Core using (Category)

open import Container.Lowering


open import Container.Lowering.Properties
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
