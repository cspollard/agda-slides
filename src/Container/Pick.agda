{-# OPTIONS --safe --without-K #-}

-- The continuation `Fin n → A` of a node of arity 2 or 4, from its children:
-- `impure (s , pick2 a b)` in the free monad of a container whose shape has positions `Fin 2`.

module Container.Pick where

open import Data.Fin using (Fin; zero; suc)

pick2 : ∀ {A : Set} → A → A → Fin 2 → A
pick2 a b zero          = a
pick2 a b (suc zero)    = b
pick2 a b (suc (suc ()))

pick4 : ∀ {A : Set} → A → A → A → A → Fin 4 → A
pick4 a b c d zero                      = a
pick4 a b c d (suc zero)                = b
pick4 a b c d (suc (suc zero))          = c
pick4 a b c d (suc (suc (suc zero)))    = d
pick4 a b c d (suc (suc (suc (suc ()))))
