{-# OPTIONS --safe --without-K #-}

-- Equality of layouts, up to an equivalence on the scalar.
--
-- A layout is plain data over the scalar, so its equality is the scalar's
-- equality `_≈_` lifted pointwise: sizes, every coordinate and length of every
-- drawing command, and every anchor box.  Labels, styles and names are compared
-- with `_≡_`.  The lifted relation is an equivalence
-- (`≈ᴸ-isEquivalence`).

open import Level using (0ℓ)
open import Relation.Binary using (Rel; IsEquivalence)

module Slides.Diagram.Equality {S : Set} {_≈_ : Rel S 0ℓ} (eq : IsEquivalence _≈_) where

open import Data.List.Relation.Binary.Pointwise as PW using (Pointwise)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Slides.Diagram.Draw

private module E = IsEquivalence eq

------------------------------------------------------------------------
-- Drawing commands

data _≈ᵈ_ : Draw S → Draw S → Set where
  rect≈   : ∀ {x x′ y y′ w w′ h h′ s} →
            x ≈ x′ → y ≈ y′ → w ≈ w′ → h ≈ h′ → rect x y w h s ≈ᵈ rect x′ y′ w′ h′ s
  circle≈ : ∀ {x x′ y y′ r r′ s} →
            x ≈ x′ → y ≈ y′ → r ≈ r′ → circle x y r s ≈ᵈ circle x′ y′ r′ s
  line≈   : ∀ {a a′ b b′ c c′ d d′ s} →
            a ≈ a′ → b ≈ b′ → c ≈ c′ → d ≈ d′ → line a b c d s ≈ᵈ line a′ b′ c′ d′ s
  arrow≈  : ∀ {a a′ b b′ c c′ d d′ s} →
            a ≈ a′ → b ≈ b′ → c ≈ c′ → d ≈ d′ → arrow a b c d s ≈ᵈ arrow a′ b′ c′ d′ s
  label≈  : ∀ {x x′ y y′ n t s} → x ≈ x′ → y ≈ y′ → label x y n t s ≈ᵈ label x′ y′ n t s

≈ᵈ-refl : ∀ {x} → x ≈ᵈ x
≈ᵈ-refl {rect _ _ _ _ _}   = rect≈ E.refl E.refl E.refl E.refl
≈ᵈ-refl {circle _ _ _ _}   = circle≈ E.refl E.refl E.refl
≈ᵈ-refl {line _ _ _ _ _}   = line≈ E.refl E.refl E.refl E.refl
≈ᵈ-refl {arrow _ _ _ _ _}  = arrow≈ E.refl E.refl E.refl E.refl
≈ᵈ-refl {label _ _ _ _ _}  = label≈ E.refl E.refl

≈ᵈ-sym : ∀ {x y} → x ≈ᵈ y → y ≈ᵈ x
≈ᵈ-sym (rect≈ a b c d) = rect≈ (E.sym a) (E.sym b) (E.sym c) (E.sym d)
≈ᵈ-sym (circle≈ a b c) = circle≈ (E.sym a) (E.sym b) (E.sym c)
≈ᵈ-sym (line≈ a b c d) = line≈ (E.sym a) (E.sym b) (E.sym c) (E.sym d)
≈ᵈ-sym (arrow≈ a b c d) = arrow≈ (E.sym a) (E.sym b) (E.sym c) (E.sym d)
≈ᵈ-sym (label≈ a b)    = label≈ (E.sym a) (E.sym b)

≈ᵈ-trans : ∀ {x y z} → x ≈ᵈ y → y ≈ᵈ z → x ≈ᵈ z
≈ᵈ-trans (rect≈ a b c d) (rect≈ a′ b′ c′ d′) = rect≈ (E.trans a a′) (E.trans b b′) (E.trans c c′) (E.trans d d′)
≈ᵈ-trans (circle≈ a b c) (circle≈ a′ b′ c′) = circle≈ (E.trans a a′) (E.trans b b′) (E.trans c c′)
≈ᵈ-trans (line≈ a b c d) (line≈ a′ b′ c′ d′) = line≈ (E.trans a a′) (E.trans b b′) (E.trans c c′) (E.trans d d′)
≈ᵈ-trans (arrow≈ a b c d) (arrow≈ a′ b′ c′ d′) = arrow≈ (E.trans a a′) (E.trans b b′) (E.trans c c′) (E.trans d d′)
≈ᵈ-trans (label≈ a b) (label≈ a′ b′) = label≈ (E.trans a a′) (E.trans b b′)

≈ᵈ-isEquivalence : IsEquivalence _≈ᵈ_
≈ᵈ-isEquivalence = record { refl = ≈ᵈ-refl ; sym = ≈ᵈ-sym ; trans = ≈ᵈ-trans }

------------------------------------------------------------------------
-- Boxes and anchors

record _≈ᵇ_ (b b′ : Box S) : Set where
  constructor box≈
  field
    left≈   : Box.left b ≈ Box.left b′
    top≈    : Box.top b ≈ Box.top b′
    width≈  : Box.width b ≈ Box.width b′
    height≈ : Box.height b ≈ Box.height b′

≈ᵇ-isEquivalence : IsEquivalence _≈ᵇ_
≈ᵇ-isEquivalence = record
  { refl  = box≈ E.refl E.refl E.refl E.refl
  ; sym   = λ { (box≈ a b c d) → box≈ (E.sym a) (E.sym b) (E.sym c) (E.sym d) }
  ; trans = λ { (box≈ a b c d) (box≈ a′ b′ c′ d′) →
                box≈ (E.trans a a′) (E.trans b b′) (E.trans c c′) (E.trans d d′) } }

-- a named anchor: the same name, equal boxes
_≈ᵃ_ : String × Box S → String × Box S → Set
x ≈ᵃ y = proj₁ x ≡ proj₁ y × proj₂ x ≈ᵇ proj₂ y

≈ᵃ-isEquivalence : IsEquivalence _≈ᵃ_
≈ᵃ-isEquivalence = record
  { refl  = ≡.refl , IsEquivalence.refl ≈ᵇ-isEquivalence
  ; sym   = λ { (p , q) → ≡.sym p , IsEquivalence.sym ≈ᵇ-isEquivalence q }
  ; trans = λ { (p , q) (p′ , q′) → ≡.trans p p′ , IsEquivalence.trans ≈ᵇ-isEquivalence q q′ } }

------------------------------------------------------------------------
-- Layouts

record _≈ᴸ_ (l l′ : Layout S) : Set where
  constructor layout≈
  field
    width≈   : Layout.width l ≈ Layout.width l′
    height≈  : Layout.height l ≈ Layout.height l′
    draws≈   : Pointwise _≈ᵈ_ (Layout.draws l) (Layout.draws l′)
    anchors≈ : Pointwise _≈ᵃ_ (Layout.anchors l) (Layout.anchors l′)

≈ᴸ-isEquivalence : IsEquivalence _≈ᴸ_
≈ᴸ-isEquivalence = record
  { refl  = layout≈ E.refl E.refl (PW.refl ≈ᵈ-refl) (PW.refl (IsEquivalence.refl ≈ᵃ-isEquivalence))
  ; sym   = λ { (layout≈ a b c d) →
                layout≈ (E.sym a) (E.sym b) (PW.symmetric ≈ᵈ-sym c)
                        (PW.symmetric (IsEquivalence.sym ≈ᵃ-isEquivalence) d) }
  ; trans = λ { (layout≈ a b c d) (layout≈ a′ b′ c′ d′) →
                layout≈ (E.trans a a′) (E.trans b b′) (PW.transitive ≈ᵈ-trans c c′)
                        (PW.transitive (IsEquivalence.trans ≈ᵃ-isEquivalence) d d′) } }
