{-# OPTIONS --safe --without-K #-}

-- Space: lengths and positions.  Layout depends on this theory only.
--
-- `Space S` is an ordered monoid of lengths (zero, `+`, frame union `⊔`, comparison), the
-- exact-subtraction layer `Sub` (centring, `atop`), and `pct p x`, "p percent of x".  `Scale`
-- is the optional layer of an ordered module over a ring of ratios `R`: ℚ over itself, and
-- also ℕ over itself (whole-number scaling).  There are no ticks here; a tick read as a
-- length is Coupling.
--
-- Signature: `SpaceC`, one command per operation; `SpaceC ⋆ V` are the symbolic scalars of a
-- layout, read by `pfold` with the handler `spaceH` of a model.  Two commands are lowered
-- along ℕ → ℚ (`Slides.Scalar.Hom`).

module Slides.Scalar.Space where

open import Level using (0ℓ)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤)
open import Data.Container.Core using (Container; _▷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
import Relation.Binary.PropositionalEquality.Properties as ≡P

open import Container.Interpret.Plain using (Handler; Congruent)
open import Slides.Scalar.Core

record Space (S : Set) : Set₁ where
  field
    ord : OrdMon S
    sub : Sub ord
    pct : ℕ → S → S
  open OrdMon ord public
  open Sub sub public
  field
    pct-100  : ∀ x → pct 100 x ≡ x
    pct-mono : ∀ p {x y} → x ≤ y → pct p x ≤ pct p y

-- An ordered module over ratios `R` (the ring operations of `R` are data; the module laws
-- are what lengths need).
record Scale {S} (M : OrdMon S) (R : Set) : Set₁ where
  open OrdMon M
  infixr 7 _·_
  field
    0r 1r : R
    _+r_ _*r_ : R → R → R
    _≤r_ : R → R → Set
    _·_ : R → S → S
    ·-1    : ∀ x → 1r · x ≡ x
    ·-zero : ∀ x → 0r · x ≡ 0#
    ·-*    : ∀ r s x → (r *r s) · x ≡ r · (s · x)
    ·-+    : ∀ r s x → (r +r s) · x ≡ r · x + s · x
    ·-dist : ∀ r x y → r · (x + y) ≡ r · x + r · y
    ·-mono : ∀ {r x y} → 0r ≤r r → x ≤ y → r · x ≤ r · y

------------------------------------------------------------------------
-- The signature

data SpaceOp : Set where
  Zero Plus Max Minus Lt : SpaceOp          -- `Lt a b x y`: `x` if `a ≤ b`, else `y`
  Pct : ℕ → SpaceOp

spaceArity : SpaceOp → Set
spaceArity Zero    = ⊥
spaceArity Plus    = Fin 2
spaceArity Max     = Fin 2
spaceArity Minus    = Fin 2
spaceArity Lt      = Fin 4
spaceArity (Pct _) = ⊤

SpaceC : Container 0ℓ 0ℓ
SpaceC = SpaceOp ▷ spaceArity

module _ {S} (Sp : Space S) where
  open Space Sp

  spaceH : Handler SpaceC S
  spaceH Zero    k = 0#
  spaceH Plus    k = k zero + k (suc zero)
  spaceH Max     k = k zero ⊔ k (suc zero)
  spaceH Minus    k = k zero - k (suc zero)
  spaceH Lt      k = select (k zero ≤? k (suc zero)) (k (suc (suc zero))) (k (suc (suc (suc zero))))
  spaceH (Pct p) k = pct p (k _)

  spaceCong : Congruent SpaceC (≡P.setoid S) spaceH
  spaceCong Zero    e = refl
  spaceCong Plus    e = cong₂ _+_ (e zero) (e (suc zero))
  spaceCong Max     e = cong₂ _⊔_ (e zero) (e (suc zero))
  spaceCong Minus    e = cong₂ _-_ (e zero) (e (suc zero))
  spaceCong Lt {k} {k′} e
    rewrite e zero | e (suc zero) | e (suc (suc zero)) | e (suc (suc (suc zero))) = refl
  spaceCong (Pct p) e = cong (pct p) (e _)
