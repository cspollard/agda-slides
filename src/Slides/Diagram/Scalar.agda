{-# OPTIONS --safe --without-K #-}

-- The scalar a layout is computed in.
--
-- `Ops S` is what the layout needs to run.  It is the combination of two *layers*, each
-- the algebra of one small signature (`Slides.Diagram.Expr` makes the signatures
-- containers, and the layers' sum is the signature of the symbolic scalars):
--
--   * `CoreOps S`: zero, sum, maximum, the literal `fromℕ n`, and "p percent of"
--     (multiplication by the literal p/100).  Every scalar has these, with the same laws;
--   * `SubOps S`: the difference.  Its symbol is one, its laws are not: in ℕ it is the monus
--     (which is only applied to a larger minuend, see `Slides.Diagram.Place`), in ℤ and ℚ
--     it is real subtraction.  That is why a map ℕ → ℚ (`Slides.Diagram.NatQ.ι`) preserves
--     the core layer unconditionally but the difference only where `b ≤ a`.
--
-- `Ops S` adds `toℕ` (the final output step; not part of any layer: it is not an
-- operation of the layout) and re-exports the fields of both layers, so `Ops._+_ O`,
-- `Ops._-_ O` read as before.  ℕ is a scalar, and so are ℤ and ℚ.
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

record CoreOps (S : Set) : Set where
  infixl 6 _+_
  infixl 7 _⊔_
  field
    0#        : S
    _+_       : S → S → S
    _⊔_       : S → S → S
    fromℕ     : ℕ → S
    -- `percentOf p x`: p percent of x
    percentOf : ℕ → S → S

  dbl : S → S
  dbl x = x + x

record SubOps (S : Set) : Set where
  infixl 6 _-_
  field
    -- exact wherever the layout uses it (the minuend is the larger)
    _-_ : S → S → S

record Ops (S : Set) : Set where
  field
    core : CoreOps S
    sub  : SubOps S
    -- for output; a negative scalar has no drawing coordinate and clamps
    toℕ  : S → ℕ
  open CoreOps core public
  open SubOps sub public

natOps : Ops ℕ
natOps = record
  { core = record { 0# = 0 ; _+_ = ℕ._+_ ; _⊔_ = ℕ._⊔_ ; fromℕ = λ n → n
                  ; percentOf = λ p x → (x ℕ.* p) ℕ./ 100 }
  ; sub = record { _-_ = ℕ._∸_ } ; toℕ = λ n → n }

intOps : Ops ℤ
intOps = record
  { core = record { 0# = ℤ.+ 0 ; _+_ = ℤ._+_ ; _⊔_ = ℤ._⊔_ ; fromℕ = ℤ.+_
                  ; percentOf = λ p x → (ℤ.+ p ℤ.* x) ℤ./ ℤ.+ 100 }
  ; sub = record { _-_ = ℤ._-_ } ; toℕ = ℤ.∣_∣ }

ratOps : Ops ℚ.ℚ
ratOps = record
  { core = record { 0# = ℚ.0ℚ ; _+_ = ℚ._+_ ; _⊔_ = ℚ._⊔_ ; fromℕ = λ n → ℤ.+ n ℚ./ 1
                  ; percentOf = λ p x → (ℤ.+ p ℚ./ 100) ℚ.* x }
  ; sub = record { _-_ = ℚ._-_ } ; toℕ = λ q → ℤ.∣ ℚ.floor q ∣ }

-- Homomorphisms of scalars, per layer: a map that commutes with every operation of the
-- layer (everything but `toℕ`, which only the final output step applies).  The equations
-- are exactly what `Slides.Diagram.LayoutNatural` needs; no order is required, because
-- layout only *computes* with the operations, and each of them is preserved on the nose.
-- The two layers are independent: the core one holds of the evaluation into ℕ, ℤ, ℚ and of
-- `ι : ℕ → ℚ` (percentages that divide evenly), the sub one of an evaluation (the
-- difference is the monus on both sides, or subtraction on both) and of `ι` only on a
-- pair with `b ≤ a`; it fails for a map ℤ → ℕ that clamps.
record IsCoreHom {S T : Set} (O : CoreOps S) (P : CoreOps T) (h : S → T) : Set where
  private module O = CoreOps O
  private module P = CoreOps P
  field
    h-0         : h O.0# ≡ P.0#
    h-+         : ∀ a b → h (a O.+ b) ≡ h a P.+ h b
    h-⊔         : ∀ a b → h (a O.⊔ b) ≡ h a P.⊔ h b
    h-fromℕ     : ∀ n → h (O.fromℕ n) ≡ P.fromℕ n
    h-percentOf : ∀ p a → h (O.percentOf p a) ≡ P.percentOf p (h a)

record IsSubHom {S T : Set} (O : SubOps S) (P : SubOps T) (h : S → T) : Set where
  private module O = SubOps O
  private module P = SubOps P
  field
    h-- : ∀ a b → h (a O.- b) ≡ h a P.- h b

-- a homomorphism of `Ops` is one of each layer (the fields are re-exported)
record IsOpsHom {S T : Set} (O : Ops S) (P : Ops T) (h : S → T) : Set where
  field
    coreHom : IsCoreHom (Ops.core O) (Ops.core P) h
    subHom  : IsSubHom (Ops.sub O) (Ops.sub P) h
  open IsCoreHom coreHom public
  open IsSubHom subHom public
