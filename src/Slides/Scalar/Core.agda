{-# OPTIONS --safe --without-K #-}

-- The ordered monoid shared by Space and Time, its exact-subtraction layer, and homomorphisms.
--
-- Lengths and durations are both a cancellative commutative monoid `(0#, +)` with a total
-- decidable order and a join `_⊔_` (frame union; the longer duration).  Subtraction is the
-- optional layer `Sub`, exact where the minuend is the larger (all ℕ's monus promises).
-- `IsOrdMonHom` is an order-embedding model homomorphism; `h-sub` shows it preserves exact
-- subtraction from the laws.  Equality is `_≡_`.

module Slides.Scalar.Core where

open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥-elim)
open import Data.Bool using (if_then_else_)
open import Relation.Nullary.Decidable using (does)

record OrdMon (S : Set) : Set₁ where
  infixl 6 _+_
  infixl 7 _⊔_
  infix 4 _≤_
  field
    0#   : S
    _+_  : S → S → S
    _⊔_  : S → S → S
    _≤_  : S → S → Set
    _≤?_ : ∀ a b → Dec (a ≤ b)
    +-assoc    : ∀ a b c → (a + b) + c ≡ a + (b + c)
    +-comm     : ∀ a b → a + b ≡ b + a
    +-idˡ      : ∀ a → 0# + a ≡ a
    +-cancelˡ  : ∀ a b c → a + b ≡ a + c → b ≡ c
    ≤-refl     : ∀ {a} → a ≤ a
    ≤-trans    : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
    ≤-antisym  : ∀ {a b} → a ≤ b → b ≤ a → a ≡ b
    ≤-total    : ∀ a b → a ≤ b ⊎ b ≤ a
    +-mono     : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d
    ⊔-ub₁      : ∀ a b → a ≤ a ⊔ b
    ⊔-ub₂      : ∀ a b → b ≤ a ⊔ b
    ⊔-lub      : ∀ {a b c} → a ≤ c → b ≤ c → a ⊔ b ≤ c

  +-idʳ : ∀ a → a + 0# ≡ a
  +-idʳ a = trans (+-comm a 0#) (+-idˡ a)

  ⊔-≤ : ∀ {a b} → a ≤ b → a ⊔ b ≡ b
  ⊔-≤ a≤b = ≤-antisym (⊔-lub a≤b ≤-refl) (⊔-ub₂ _ _)

  ⊔-≥ : ∀ {a b} → b ≤ a → a ⊔ b ≡ a
  ⊔-≥ b≤a = ≤-antisym (⊔-lub ≤-refl b≤a) (⊔-ub₁ _ _)

  -- comparison as a select: `select (a ≤? b) x y` is `x` if `a ≤ b`, else `y`
  select : ∀ {A : Set} {a b} → Dec (a ≤ b) → A → A → A
  select d x y = if does d then x else y

-- Exact subtraction, as an optional layer over an ordered monoid.
record Sub {S} (M : OrdMon S) : Set where
  open OrdMon M
  infixl 6 _-_
  field
    _-_     : S → S → S
    sub-add : ∀ {a b} → b ≤ a → b + (a - b) ≡ a

  sub-unique : ∀ {a b d} → b ≤ a → b + d ≡ a → d ≡ a - b
  sub-unique {a} {b} b≤a e = +-cancelˡ b _ _ (trans e (sym (sub-add b≤a)))

  sub-self : ∀ a → a - a ≡ 0#
  sub-self a = sym (sub-unique ≤-refl (+-idʳ a))

-- A model homomorphism of ordered monoids: an order embedding.
record IsOrdMonHom {A B} (M : OrdMon A) (N : OrdMon B) (h : A → B) : Set where
  private module M = OrdMon M ; module N = OrdMon N
  field
    h-0       : h M.0# ≡ N.0#
    h-+       : ∀ a b → h (a M.+ b) ≡ h a N.+ h b
    h-mono    : ∀ {a b} → a M.≤ b → h a N.≤ h b
    h-reflect : ∀ {a b} → h a N.≤ h b → a M.≤ b

  -- The join is preserved, from monotonicity and totality alone.
  h-⊔ : ∀ a b → h (a M.⊔ b) ≡ h a N.⊔ h b
  h-⊔ a b with M.≤-total a b
  ... | inj₁ a≤b = trans (cong h (M.⊔-≤ a≤b)) (sym (N.⊔-≤ (h-mono a≤b)))
  ... | inj₂ b≤a = trans (cong h (M.⊔-≥ b≤a)) (sym (N.⊔-≥ (h-mono b≤a)))

  -- Comparison is preserved: the select reads the same on both sides.
  h-select : ∀ {X : Set} {a b} (da : Dec (a M.≤ b)) (db : Dec (h a N.≤ h b))
             (x y : X) → M.select da x y ≡ N.select db x y
  h-select (yes _) (yes _) x y = refl
  h-select (no _)  (no _)  x y = refl
  h-select (yes p) (no ¬q) x y = ⊥-elim (¬q (h-mono p))
  h-select (no ¬p) (yes q) x y = ⊥-elim (¬p (h-reflect q))

  -- Exact subtraction is preserved where it is exact (`b ≤ a`): unconditional elsewhere is
  -- not claimed (ℕ's monus is not ℚ's difference).
  h-sub : (SM : Sub M) (SN : Sub N) → ∀ {a b} → b M.≤ a →
          h (Sub._-_ SM a b) ≡ Sub._-_ SN (h a) (h b)
  h-sub SM SN {a} {b} b≤a =
    N.+-cancelˡ (h b) _ _
      (trans (sym (h-+ b _)) (trans (cong h (Sub.sub-add SM b≤a)) (sym (Sub.sub-add SN (h-mono b≤a)))))

------------------------------------------------------------------------
-- Signatures: handlers and their sum

-- The term language over a signature `C` is `C ⋆ V` (free monad), read by `pfold` with a
-- `Handler`; a handler for a sum of signatures is a pair, and is congruent when both are.

open import Level using (0ℓ)
open import Data.Container.Core using (Container)
open import Data.Container.Combinator using () renaming (_⊎_ to _⊎ᶜ_)
open import Container.Interpret.Plain using (Handler; Congruent)
import Relation.Binary.PropositionalEquality.Properties as ≡P

infixr 5 _⊕_
_⊕_ : ∀ {C D : Container 0ℓ 0ℓ} {A : Set} → Handler C A → Handler D A → Handler (C ⊎ᶜ D) A
(h ⊕ g) (inj₁ a) k = h a k
(h ⊕ g) (inj₂ a) k = g a k

⊕-cong : ∀ {C D : Container 0ℓ 0ℓ} {A : Set} {h : Handler C A} {g : Handler D A} →
         Congruent C (≡P.setoid A) h → Congruent D (≡P.setoid A) g → Congruent (C ⊎ᶜ D) (≡P.setoid A) (h ⊕ g)
⊕-cong ch cg (inj₁ a) = ch a
⊕-cong ch cg (inj₂ a) = cg a
