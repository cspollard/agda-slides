{-# OPTIONS --safe --without-K #-}

-- Control for ../TwoCommandsOneInput.agda: MUST typecheck (same stand-ins, an injective table).

module DistinctInputsOk where

open import Data.Fin using (Fin; zero; suc)
open import Data.Unit using (tt)   -- brings the instance of ⊤ into scope
open import Data.Fin.Properties using (all?) renaming (_≟_ to _≟F_)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (True; _→-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_)

Cmd Key : Set
Cmd = Fin 4
Key = Fin 4

conflict? : (t : Cmd → Key) → Dec (∀ i j → t i ≡ t j → i ≡ j)
conflict? t = all? λ i → all? λ j → (t i ≟F t j) →-dec (i ≟F j)

record Binding : Set where
  field table : Cmd → Key

bind : (t : Cmd → Key) {{_ : True (conflict? t)}} → Binding
bind t = record { table = t }

distinct : Cmd → Key
distinct k = k

ok : Binding
ok = bind distinct
