{-# OPTIONS --safe --without-K #-}

-- Time is a parameter (`docs/Time.md` section 7): the model record of the layered time theory.
--
-- A `Clock` is a time domain `T` together with
--   * the scalar layers of `Slides.Diagram.Ordered` (`OOps T`: the ordered monoid core `0#`, `+`, `⊔`,
--     the tick embedding `fromℕ`, the subtraction, `Lt`/`Min`, floor/mod) and its laws (`QLaws`):
--     the existing model record is reused, not repeated;
--   * the order as a boolean `_<ᵇ_`, the one `lt` selects on (`lt-spec`): the select form stays the
--     algebraic one, the guards of the temporal semantics read the same comparison;
--   * the tick clock `ι = fromℕ : ℕ → T` and the homomorphism laws the proofs use: `0`, `+`, the
--     order (unconditionally) and the exact case of subtraction (`b ≤ a`; the ℕ side is a monus).
-- Density, induction, scaling and easing are *not* in the record: a model-specific fact is a named
-- hypothesis of the lemma that needs it (`Slides.Anim.Track`: the `Scale`/`Ease` layers are ℚ only).
--
-- `Sem K` is the temporal skeleton read in a clock: a timed value is a duration in ticks and a
-- function of time; `seqAt` offsets time by the first duration, `parAt` shares it and overlays,
-- absence being the unit.  The instance is ℚ (`Slides.Time.Rat`); its laws are `Slides.Time.Properties`.

module Slides.Time where

open import Data.Bool using (Bool; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Slides.Diagram.Scalar using (Ops)
open import Slides.Diagram.Ordered using (OOps; QLaws; module OrdOps)

record Clock : Set₁ where
  field
    T    : Set
    O    : OOps T
    _<ᵇ_ : T → T → Bool
  open Ops (OOps.ops O) public
  open OrdOps (OOps.ord O) using (lt)

  -- the tick clock
  ι : ℕ → T
  ι = fromℕ

  field
    laws    : QLaws O
    lt-spec : ∀ a b x y → lt a b x y ≡ (if a <ᵇ b then x else y)
    ι-0     : ι 0 ≡ 0#
    ι-+     : ∀ m n → ι (m ℕ.+ n) ≡ ι m + ι n
    ι-<ᵇ    : ∀ m n → (ι m <ᵇ ι n) ≡ (m ℕ.<ᵇ n)
    ι-∸     : ∀ m n → n ℕ.≤ m → ι (m ℕ.∸ n) ≡ ι m - ι n

-- what is shown when at most one of two parts is running, or both: they go over each other
mergeM : ∀ {F : Set} → (F → F → F) → Maybe F → Maybe F → Maybe F
mergeM _⊙_ nothing  y        = y
mergeM _⊙_ x        nothing  = x
mergeM _⊙_ (just x) (just y) = just (x ⊙ y)

module Sem (K : Clock) where
  open Clock K

  -- a length in ticks and a function of time
  Timed : Set → Set
  Timed A = ℕ × (T → A)

  seqAt : ∀ {A} → Timed A → Timed A → Timed A
  seqAt (n , f) (m , g) = n ℕ.+ m , λ τ → if τ <ᵇ ι n then f τ else g (τ - ι n)

  parAt : ∀ {F : Set} → (F → F → F) → Timed (Maybe F) → Timed (Maybe F) → Timed (Maybe F)
  parAt _⊙_ (n , f) (m , g) = n ℕ.⊔ m , λ τ → mergeM _⊙_ (f τ) (g τ)
