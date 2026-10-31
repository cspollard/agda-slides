{-# OPTIONS --safe --without-K #-}

-- The ordered monoid shared by Space and Time, optional exact subtraction, and homomorphisms.
--
--   OrdMon S     a cancellative commutative monoid (`0#`, `+`), a decidable total order, and the join
--                `_⊔_` (frame union; the longer duration), as stdlib structures over `_≡_`
--                (`IsCommutativeMonoid`, `IsDecTotalOrder`, `Supremum`): the laws are those
--                projections, renamed (`+-assoc`, `≤-trans`, `⊔-comm`, ...) so clients read as before
--   Sub M        exact subtraction: `b ≤ a → b + (a - b) ≡ a` (all that ℕ's monus promises)
--   IsOrdMonHom  an order monomorphism that is a monoid homomorphism; from the laws alone `h-⊔`,
--                `h-select` (comparison) and, where exact, `h-sub` follow
--
-- Categorical reading (Hyland–Power 2007): `SpaceC`/`TimeC` are the operations of a signature, an
-- `OrdMon` with its extras is an algebra for it satisfying the equations (a model of the theory),
-- and an `IsOrdMonHom` is an algebra morphism that also reflects order.
--
-- Also the sum `_⊕_` of handlers for a sum of signatures, congruent when both are (`⊕-cong`).

module Slides.Scalar.Core where

open import Level using (0ℓ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Binary.Lattice using (Supremum; JoinSemilattice)
open import Relation.Binary.Structures using (IsDecTotalOrder)
open import Relation.Binary.Morphism.Structures using (IsOrderMonomorphism)
open import Algebra.Bundles using (CommutativeMonoid)
open import Algebra.Structures using (IsCommutativeMonoid)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
import Algebra.Properties.CommutativeSemigroup as CSP
import Relation.Binary.Lattice.Properties.JoinSemilattice as JSP
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
    isCommutativeMonoid : IsCommutativeMonoid _≡_ _+_ 0#
    +-cancelˡ           : ∀ a b c → a + b ≡ a + c → b ≡ c
    isDecTotalOrder     : IsDecTotalOrder _≡_ _≤_
    +-mono              : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d
    supremum            : Supremum _≤_ _⊔_

  open IsCommutativeMonoid isCommutativeMonoid public using ()
    renaming (assoc to +-assoc; comm to +-comm; identityˡ to +-idˡ; identityʳ to +-idʳ)
  open IsDecTotalOrder isDecTotalOrder public using (_≤?_)
    renaming (refl to ≤-refl; trans to ≤-trans; antisym to ≤-antisym; total to ≤-total; reflexive to ≤-reflexive)

  ⊔-ub₁ : ∀ a b → a ≤ a ⊔ b
  ⊔-ub₁ a b = proj₁ (supremum a b)
  ⊔-ub₂ : ∀ a b → b ≤ a ⊔ b
  ⊔-ub₂ a b = proj₁ (proj₂ (supremum a b))
  ⊔-lub : ∀ {a b c} → a ≤ c → b ≤ c → a ⊔ b ≤ c
  ⊔-lub {a} {b} = proj₂ (proj₂ (supremum a b)) _

  commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
  commutativeMonoid = record { isCommutativeMonoid = isCommutativeMonoid }

  rawMonoid = CommutativeMonoid.rawMonoid commutativeMonoid

  joinSemilattice : JoinSemilattice 0ℓ 0ℓ 0ℓ
  joinSemilattice = record
    { _∨_ = _⊔_
    ; isJoinSemilattice = record { isPartialOrder = IsDecTotalOrder.isPartialOrder isDecTotalOrder ; supremum = supremum } }

  -- the library's laws of `+` and `⊔`, under our names
  open CSP (CommutativeMonoid.commutativeSemigroup commutativeMonoid) public using () renaming (interchange to +-interchange)
  open JSP joinSemilattice public using () renaming (∨-comm to ⊔-comm; ∨-assoc to ⊔-assoc; x≤y⇒x∨y≈y to ⊔-≤)

  ⊔-≥ : ∀ {a b} → b ≤ a → a ⊔ b ≡ a
  ⊔-≥ {a} b≤a = trans (⊔-comm a _) (⊔-≤ b≤a)

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

  -- differences compose along `x ≤ y ≤ z`
  sub-trans : ∀ {x y z} → x ≤ y → y ≤ z → (y - x) + (z - y) ≡ z - x
  sub-trans {x} {y} {z} x≤y y≤z =
    sub-unique (≤-trans x≤y y≤z)
      (trans (sym (+-assoc x (y - x) (z - y))) (trans (cong (_+ (z - y)) (sub-add x≤y)) (sub-add y≤z)))

-- A model homomorphism of ordered monoids: a monoid homomorphism that is an order monomorphism.
record IsOrdMonHom {A B} (M : OrdMon A) (N : OrdMon B) (h : A → B) : Set where
  private module M = OrdMon M ; module N = OrdMon N
  open MonoidMorphisms M.rawMonoid N.rawMonoid using (IsMonoidHomomorphism; module IsMonoidHomomorphism)
  field
    isMonoidHom : IsMonoidHomomorphism h
    isOrderMono : IsOrderMonomorphism _≡_ _≡_ M._≤_ N._≤_ h

  h-0    : h M.0# ≡ N.0#
  h-0    = IsMonoidHomomorphism.ε-homo isMonoidHom
  h-+    : ∀ a b → h (a M.+ b) ≡ h a N.+ h b
  h-+    = IsMonoidHomomorphism.homo isMonoidHom
  h-mono : ∀ {a b} → a M.≤ b → h a N.≤ h b
  h-mono = IsOrderMonomorphism.mono isOrderMono
  h-reflect : ∀ {a b} → h a N.≤ h b → a M.≤ b
  h-reflect = IsOrderMonomorphism.cancel isOrderMono

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

-- Build one from the four laws: `cong` is `cong h`, injectivity is antisymmetry of the two reflections.
ordMonHom : ∀ {A B} (M : OrdMon A) (N : OrdMon B) (h : A → B) →
  h (OrdMon.0# M) ≡ OrdMon.0# N →
  (∀ a b → h (OrdMon._+_ M a b) ≡ OrdMon._+_ N (h a) (h b)) →
  (∀ {a b} → OrdMon._≤_ M a b → OrdMon._≤_ N (h a) (h b)) →
  (∀ {a b} → OrdMon._≤_ N (h a) (h b) → OrdMon._≤_ M a b) → IsOrdMonHom M N h
ordMonHom M N h z p mo re = record
  { isMonoidHom = record { isMagmaHomomorphism = record { isRelHomomorphism = record { cong = cong h } ; homo = p } ; ε-homo = z }
  ; isOrderMono = record
      { isOrderHomomorphism = record { cong = cong h ; mono = mo }
      ; injective = λ e → OrdMon.≤-antisym M (re (OrdMon.≤-reflexive N e)) (re (OrdMon.≤-reflexive N (sym e)))
      ; cancel = re } }

-- A handler for a sum of signatures is a pair of handlers.

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
