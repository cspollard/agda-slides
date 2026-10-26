{-# OPTIONS --safe --without-K #-}

-- The scalar a layout is computed in.
--
-- `Ops S` is what the layout needs to run: zero, sum, difference, maximum,
-- conversion from and to the naturals the deck's numbers are written in, and
-- "p percent of".  ℕ is a scalar (its difference is the monus, which is only
-- applied to a larger minuend; see `Slides.Diagram.Place`), and so are ℤ and ℚ.
--
-- Layouts keep positions in half units (see `Slides.Diagram.Place`), so no
-- scalar needs a division by two: the "doubling trick".  What a scalar can
-- *prove* is a separate matter: `Slides.Diagram.Laws` states the laws of the
-- layout operations for a scalar that is a commutative ring under `_≡_`
-- (ℤ is; ℕ is not, so it runs but is not covered by those proofs).

module Slides.Diagram.Scalar where

open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)
import Data.Integer.DivMod as ℤ
import Data.Rational as ℚ
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (_≡_)

record Ops (S : Set) : Set where
  infixl 6 _+_ _-_
  infixl 7 _⊔_
  field
    0#        : S
    _+_       : S → S → S
    -- exact wherever the layout uses it (the minuend is the larger)
    _-_       : S → S → S
    _⊔_       : S → S → S
    fromℕ     : ℕ → S
    -- for output; a negative scalar has no drawing coordinate and clamps
    toℕ       : S → ℕ
    -- `percentOf p x`: p percent of x
    percentOf : ℕ → S → S

  dbl : S → S
  dbl x = x + x

natOps : Ops ℕ
natOps = record
  { 0# = 0 ; _+_ = ℕ._+_ ; _-_ = ℕ._∸_ ; _⊔_ = ℕ._⊔_
  ; fromℕ = λ n → n ; toℕ = λ n → n
  ; percentOf = λ p x → (x ℕ.* p) ℕ./ 100 }

intOps : Ops ℤ
intOps = record
  { 0# = ℤ.+ 0 ; _+_ = ℤ._+_ ; _-_ = ℤ._-_ ; _⊔_ = ℤ._⊔_
  ; fromℕ = ℤ.+_ ; toℕ = ℤ.∣_∣
  ; percentOf = λ p x → (ℤ.+ p ℤ.* x) ℤ./ ℤ.+ 100 }

ratOps : Ops ℚ.ℚ
ratOps = record
  { 0# = ℚ.0ℚ ; _+_ = ℚ._+_ ; _-_ = ℚ._-_ ; _⊔_ = ℚ._⊔_
  ; fromℕ = λ n → ℤ.+ n ℚ./ 1 ; toℕ = λ q → ℤ.∣ ℚ.floor q ∣
  ; percentOf = λ p x → (ℤ.+ p ℚ./ 100) ℚ.* x }

-- A homomorphism of scalars: a map that commutes with every operation the layout
-- uses (everything but `toℕ`, which only the final output step applies).  The
-- equations are exactly what `Slides.Diagram.LayoutNatural` needs; no order is
-- required, because layout only *computes* with the operations, and each of them
-- is preserved on the nose.  (Preserving `-` as `_≡_` is a real condition: it
-- holds for the evaluation of `Slides.Diagram.Expr` into ℕ, whose difference is
-- the monus on both sides, and fails for a map ℤ → ℕ that clamps.)
record IsOpsHom {S T : Set} (O : Ops S) (P : Ops T) (h : S → T) : Set where
  private module O = Ops O
  private module P = Ops P
  field
    h-0         : h O.0# ≡ P.0#
    h-+         : ∀ a b → h (a O.+ b) ≡ h a P.+ h b
    h--         : ∀ a b → h (a O.- b) ≡ h a P.- h b
    h-⊔         : ∀ a b → h (a O.⊔ b) ≡ h a P.⊔ h b
    h-fromℕ     : ∀ n → h (O.fromℕ n) ≡ P.fromℕ n
    h-percentOf : ∀ p a → h (O.percentOf p a) ≡ P.percentOf p (h a)
