{-# OPTIONS --safe --without-K #-}

-- Must NOT typecheck: two commands bound to the same input (`next` and `prev` both on the
-- right arrow).  The binding is accepted only when its (finite) table is injective, checked
-- by computation like `Slides.Anim.Render.Uniform`: the instance argument is `⊤` when the
-- table is injective and has no instance otherwise, so the error is "No instance of type"
-- and this file fits `make test-negative` unchanged once its stand-ins are replaced.
--
-- TODO(Stage 1 port): `Cmd`, `Key`, `Binding` and `bind` are local stand-ins for the
-- commands of `Slides.Input.Nav`, the inputs of a backend and `Slides.Input.Supports.bind`
-- (by kind; families such as `goto n` go through a decoder, see plan/Unify.md section 4b).
-- Once the real interface exists use it, then move this file to tests/negative/.

module TwoCommandsOneInput where

open import Data.Fin using (Fin; zero; suc)
open import Data.Unit using (tt)   -- brings the instance of ⊤ into scope
open import Data.Fin.Properties using (all?) renaming (_≟_ to _≟F_)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (True; _→-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- the commands (indices of the finite table) and the physical inputs
Cmd Key : Set
Cmd = Fin 4     -- next prev first last
Key = Fin 4     -- right-arrow left-arrow home end

-- a binding table is conflict-free when it is injective
conflict? : (t : Cmd → Key) → Dec (∀ i j → t i ≡ t j → i ≡ j)
conflict? t = all? λ i → all? λ j → (t i ≟F t j) →-dec (i ≟F j)

record Binding : Set where
  field table : Cmd → Key

-- the check at binding: the instance argument is `⊤` exactly when the table is injective
bind : (t : Cmd → Key) {{_ : True (conflict? t)}} → Binding
bind t = record { table = t }

-- next and prev both on the right arrow (key 0)
clash : Cmd → Key
clash zero             = zero
clash (suc zero)       = zero
clash (suc (suc zero)) = suc (suc zero)
clash _                = suc (suc (suc zero))

bad : Binding
bad = bind clash
