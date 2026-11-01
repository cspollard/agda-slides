{-# OPTIONS --safe --without-K #-}

-- Images: pictures with no syntax (Elliott, `plans/Image.md` §1-2).
--
--   Image Pt    functions `Pt → A` into a monoid `A`; the pointwise (power) monoid of `A` (stdlib
--               `Algebra.Construct.Pointwise`), so every monoid law of `A` holds for images.
--               Equality is pointwise in `A`'s own equality (a setoid), so a colour model need
--               not use `≡`
--   reindex f   precomposition `im ∘ f`: contravariant in space, a monoid homomorphism
--               (`reindex-∙`, `reindex-ε`); a transformation acts by reindexing along its inverse
--   denote      the meaning of a list of items, given the meaning of one: `prim x₁ ∙ (prim x₂ ∙ …)`
--               (the later item is the one `∙` puts on top: `∙` is "then", Porter-Duff `over` flipped)
--   denote-isMonoidHomomorphism   from `List X` under `++` into images
--   denote-rel  the logical relation: items related by any relation closed under `∙` and `ε` have
--               related meanings.  Equivariance and naturality of a drawing's meaning are instances
--               (`Slides.Diagram.Image`).

open import Algebra.Bundles using (Monoid)

open import Level using (Level)

module Semantics.Image {c ℓ : Level} (M : Monoid c ℓ) where

open import Data.List.Base using (List; []; _∷_; _++_; map)
import Data.List.Properties as ListP
import Algebra.Construct.Pointwise as Pointwise
import Algebra.Morphism.Structures as Morphisms
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private variable
  Pt Pt′ X Y : Set

Image : Set → Set c
Image Pt = Pt → Monoid.Carrier M

-- the pointwise monoid; `_≈_`, `_∙_`, `ε` are its equality, product and unit
IM : Set → Monoid c ℓ
IM Pt = Pointwise.monoid Pt M

module IMon {Pt} = Monoid (IM Pt)
open IMon using (_≈_; _∙_; ε) public

reindex : (Pt → Pt′) → Image Pt′ → Image Pt
reindex f im = λ p → im (f p)

reindex-∙ : ∀ (f : Pt → Pt′) (a b : Image Pt′) → reindex f (a ∙ b) ≈ reindex f a ∙ reindex f b
reindex-∙ f a b p = Monoid.refl M

reindex-ε : ∀ (f : Pt → Pt′) → reindex f ε ≈ ε
reindex-ε f p = Monoid.refl M

-- the meaning of a list, a fold of the meaning of an item
denote : (X → Image Pt) → List X → Image Pt
denote prim []       = ε
denote prim (x ∷ xs) = prim x ∙ denote prim xs

denote-++ : ∀ (prim : X → Image Pt) xs ys → denote prim (xs ++ ys) ≈ denote prim xs ∙ denote prim ys
denote-++ prim []       ys = IMon.sym (IMon.identityˡ _)
denote-++ prim (x ∷ xs) ys = IMon.trans (IMon.∙-congˡ (denote-++ prim xs ys)) (IMon.sym (IMon.assoc _ _ _))

denote-cong : ∀ (prim : X → Image Pt) {xs ys} → xs ≡ ys → denote prim xs ≈ denote prim ys
denote-cong prim refl = IMon.refl

module _ (prim : X → Image Pt) where
  open Morphisms.MonoidMorphisms (Monoid.rawMonoid (ListP.++-monoid X)) (Monoid.rawMonoid (IM Pt))
  open Morphisms.MagmaMorphisms (Monoid.rawMagma (ListP.++-monoid X)) (Monoid.rawMagma (IM Pt))

  denote-isMonoidHomomorphism : IsMonoidHomomorphism (denote prim)
  denote-isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = denote-cong prim }
        ; homo = denote-++ prim }
    ; ε-homo = IMon.refl }

-- items related by a relation closed under `∙` and `ε` have related meanings
denote-rel : ∀ (R : Image Pt → Image Pt′ → Set ℓ) (p : X → Image Pt) (q : Y → Image Pt′) (f : X → Y) →
             R ε ε → (∀ {a a′ b b′} → R a a′ → R b b′ → R (a ∙ b) (a′ ∙ b′)) →
             (∀ x → R (p x) (q (f x))) → ∀ xs → R (denote p xs) (denote q (map f xs))
denote-rel R p q f Rε R∙ Rp []       = Rε
denote-rel R p q f Rε R∙ Rp (x ∷ xs) = R∙ (Rp x) (denote-rel R p q f Rε R∙ Rp xs)
