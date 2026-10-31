{-# OPTIONS --safe --without-K #-}

-- Valid diagrams and the units of the empty diagram.
--
-- Valid diagrams (every sized leaf has non-negative size) and the units of the empty diagram.
--
-- `Space` does not make sizes non-negative (ℚ has negative lengths), so that is a predicate on
-- diagrams: `Valid d` is the fold of the signature into `Set`.  Its theorem is `valid-size`,
-- `valid-layout`: a valid diagram has a non-negative frame (by `pfold-rel`, using `nn+`, `nn⊔`).
--
-- Units, at the level of layouts, with `empty = spacer 0 0` (a term `besideA al empty d` is not
-- the term `d`); the hypotheses are needed because `0 ⊔ x` is `x` only if `0 ≤ x`:
--
--   besideA al empty a ≡ a ≡ besideA al a empty     if 0 ≤ height a      (`besideA-unitˡ`, `-unitʳ`)
--   aboveA  al empty a ≡ a ≡ aboveA  al a empty     if 0 ≤ width a       (`aboveA-unitˡ`, `-unitʳ`)
--   atop empty a ≡ a ≡ atop a empty                 if 0 ≤ width a, 0 ≤ height a  (`atop-unitˡ`, `-unitʳ`)
--
-- They hold for every valid diagram (`layout-beside-unitˡ`, ...).  Spacers add with no
-- hypothesis (`gap-beside`, `gap-above`, `gap-atop`).

open import Slides.Scalar.Space using (Space)

module Slides.Diagram.Valid {S : Set} (Sp : Space S) where

open import Data.Empty using (⊥)
open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; map; _++_)
import Data.List.Properties as ListP
open import Level using (0ℓ)
open import Algebra.Bundles using (Monoid)
open import Slides.Diagram.Geometry using (VAlign; Align)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Container.Interpret.Plain using (Handler; pfold; pfold-rel)
open import Slides.Diagram.Draw
open import Slides.Diagram.Syntax
open Space Sp
import Slides.Diagram.Place Sp as P
open P using (dbl; valignOffset; alignOffset)
open import Slides.Diagram.Layout Sp using (layout)
open import Slides.Diagram.Assoc Sp using (besideA-assoc; aboveA-assoc)
open import Slides.Diagram.Laws Sp using (size; sizeH; size-layout; shift-zero)

-- Valid diagrams

NN : S → Set
NN x = 0# ≤ x

nn+ : ∀ {a b} → NN a → NN b → NN (a + b)
nn+ pa pb = ≤-trans (≤-reflexive (sym (+-idˡ 0#))) (+-mono pa pb)

nn⊔ˡ : ∀ {a b} → NN a → NN (a ⊔ b)
nn⊔ˡ pa = ≤-trans pa (⊔-ub₁ _ _)

-- the extent of any list of coordinates is non-negative: it is at least the unit `0`
nn-extent : ∀ xs → NN (P.extent xs)
nn-extent []       = ≤-refl
nn-extent (x ∷ xs) = ≤-trans (nn-extent xs) (⊔-ub₂ _ _)

okH : Handler (DiagramC S) Set
okH (Rectangle w h _)     k = NN w × NN h
okH (Segment w h _)       k = NN w × NN h
okH (Disc r _)            k = NN r
okH (Text w h _ _ _)      k = NN w × NN h
okH (Ellipse a b _)       k = NN a × NN b
okH (Polyline _ _ _)      k = ⊤                    -- the frame reaches 0 and every point
okH (Path w h _ _)        k = NN w × NN h
okH (Spacer w h)          k = NN w × NN h
okH (Beside _)            k = k zero × k (suc zero)
okH (Above _)             k = k zero × k (suc zero)
okH Atop                  k = k zero × k (suc zero)
okH LabelAbove            k = k zero × k (suc zero)
okH LabelBelow            k = k zero × k (suc zero)
okH (Place w h _ _)       k = NN w × NN h
okH (Overlay w h)         k = NN w × NN h
okH (Named _)             k = k tt
okH (Connect _ _ _ _ _)   k = k tt

Valid : Dia S → Set
Valid = pfold (DiagramC S) okH (λ ())

-- the frame of a valid diagram is non-negative
valid-size : ∀ d → Valid d → NN (proj₁ (size d)) × NN (proj₂ (size d))
valid-size = pfold-rel (λ s v → v → NN (proj₁ s) × NN (proj₂ s)) hom (λ ())
  where
    hom : ∀ o k k′ → (∀ q → k′ q → NN (proj₁ (k q)) × NN (proj₂ (k q))) →
          okH o k′ → NN (proj₁ (sizeH o k)) × NN (proj₂ (sizeH o k))
    hom (Rectangle _ _ _) k k′ e p = p
    hom (Segment _ _ _)   k k′ e p = p
    hom (Disc _ _)        k k′ e p = nn+ p p , nn+ p p
    hom (Text _ _ _ _ _)  k k′ e p = p
    hom (Ellipse _ _ _)   k k′ e (p , q) = nn+ p p , nn+ q q
    hom (Polyline _ ps _) k k′ e _ = nn-extent (map proj₁ ps) , nn-extent (map proj₂ ps)
    hom (Path _ _ _ _)    k k′ e p = p
    hom (Spacer _ _)      k k′ e p = p
    hom (Beside _)        k k′ e (p , q) = nn+ (proj₁ (e zero p)) (proj₁ (e (suc zero) q)) , nn⊔ˡ (proj₂ (e zero p))
    hom (Above _)         k k′ e (p , q) = nn⊔ˡ (proj₁ (e zero p)) , nn+ (proj₂ (e zero p)) (proj₂ (e (suc zero) q))
    hom Atop              k k′ e (p , q) = nn⊔ˡ (proj₁ (e zero p)) , nn⊔ˡ (proj₂ (e zero p))
    hom LabelAbove        k k′ e (p , q) =
      nn⊔ˡ (proj₁ (e zero p)) , nn+ (proj₂ (e zero p)) (nn+ (proj₂ (e (suc zero) q)) (proj₂ (e zero p)))
    hom LabelBelow        k k′ e (p , q) =
      nn⊔ˡ (proj₁ (e zero p)) , nn+ (proj₂ (e zero p)) (nn+ (proj₂ (e (suc zero) q)) (proj₂ (e zero p)))
    hom (Place _ _ _ _)   k k′ e p = p
    hom (Overlay _ _)     k k′ e p = p
    hom (Named _)         k k′ e p = e tt p
    hom (Connect _ _ _ _ _) k k′ e p = e tt p

valid-layout : ∀ d → Valid d → NN (P.width (layout d)) × NN (P.height (layout d))
valid-layout d v = subst (λ s → NN (proj₁ s) × NN (proj₂ s)) (sym (size-layout d)) (valid-size d v)

-- The empty layout is a unit, where the frame is non-negative

empty : Layout S
empty = P.spacer 0# 0#

dbl-zero : dbl 0# ≡ 0#
dbl-zero = +-idˡ 0#

valign-self : ∀ al x → valignOffset al x x ≡ 0#
valign-self top    x = refl
valign-self middle x = sub-self x
valign-self bottom x = trans (cong dbl (sub-self x)) dbl-zero

align-self : ∀ al x → alignOffset al x x ≡ 0#
align-self left    x = refl
align-self centred x = sub-self x
align-self right   x = trans (cong dbl (sub-self x)) dbl-zero

besideA-unitˡ : ∀ al a → NN (P.height a) → P.besideA al empty a ≡ a
besideA-unitˡ al (mkLayout w h ds as) 0≤h
  rewrite ⊔-≤ 0≤h | +-idˡ w | dbl-zero | valign-self al h | +-idˡ 0# = shift-zero (mkLayout w h ds as)

besideA-unitʳ : ∀ al a → NN (P.height a) → P.besideA al a empty ≡ a
besideA-unitʳ al (mkLayout w h ds as) 0≤h
  rewrite ⊔-≥ 0≤h | +-idʳ w | valign-self al h
  = trans (cong₂ (mkLayout w h) (ListP.++-identityʳ _) (ListP.++-identityʳ _)) (shift-zero (mkLayout w h ds as))

aboveA-unitˡ : ∀ al a → NN (P.width a) → P.aboveA al empty a ≡ a
aboveA-unitˡ al (mkLayout w h ds as) 0≤w
  rewrite ⊔-≤ 0≤w | +-idˡ h | dbl-zero | align-self al w | +-idˡ 0# = shift-zero (mkLayout w h ds as)

aboveA-unitʳ : ∀ al a → NN (P.width a) → P.aboveA al a empty ≡ a
aboveA-unitʳ al (mkLayout w h ds as) 0≤w
  rewrite ⊔-≥ 0≤w | +-idʳ h | align-self al w
  = trans (cong₂ (mkLayout w h) (ListP.++-identityʳ _) (ListP.++-identityʳ _)) (shift-zero (mkLayout w h ds as))

atop-unitˡ : ∀ a → NN (P.width a) → NN (P.height a) → P.atop empty a ≡ a
atop-unitˡ (mkLayout w h ds as) 0≤w 0≤h
  rewrite ⊔-≤ 0≤w | ⊔-≤ 0≤h | sub-self w | sub-self h = shift-zero (mkLayout w h ds as)

atop-unitʳ : ∀ a → NN (P.width a) → NN (P.height a) → P.atop a empty ≡ a
atop-unitʳ (mkLayout w h ds as) 0≤w 0≤h
  rewrite ⊔-≥ 0≤w | ⊔-≥ 0≤h | sub-self w | sub-self h
  = trans (cong₂ (mkLayout w h) (ListP.++-identityʳ _) (ListP.++-identityʳ _)) (shift-zero (mkLayout w h ds as))

-- ... for the layouts of valid diagrams, with the empty diagram `spacer 0 0`
layout-beside-unitˡ : ∀ al d → Valid d → layout (besideA al (spacer 0# 0#) d) ≡ layout d
layout-beside-unitˡ al d v = besideA-unitˡ al (layout d) (proj₂ (valid-layout d v))

layout-beside-unitʳ : ∀ al d → Valid d → layout (besideA al d (spacer 0# 0#)) ≡ layout d
layout-beside-unitʳ al d v = besideA-unitʳ al (layout d) (proj₂ (valid-layout d v))

layout-above-unitˡ : ∀ al d → Valid d → layout (aboveA al (spacer 0# 0#) d) ≡ layout d
layout-above-unitˡ al d v = aboveA-unitˡ al (layout d) (proj₁ (valid-layout d v))

layout-above-unitʳ : ∀ al d → Valid d → layout (aboveA al d (spacer 0# 0#)) ≡ layout d
layout-above-unitʳ al d v = aboveA-unitʳ al (layout d) (proj₁ (valid-layout d v))

layout-atop-unitˡ : ∀ d → Valid d → layout (atop (spacer 0# 0#) d) ≡ layout d
layout-atop-unitˡ d v = atop-unitˡ (layout d) (proj₁ (valid-layout d v)) (proj₂ (valid-layout d v))

layout-atop-unitʳ : ∀ d → Valid d → layout (atop d (spacer 0# 0#)) ≡ layout d
layout-atop-unitʳ d v = atop-unitʳ (layout d) (proj₁ (valid-layout d v)) (proj₂ (valid-layout d v))

-- Gaps add (no hypothesis: a spacer draws nothing)

gap-beside : ∀ al a b → P.besideA al (P.spacer a 0#) (P.spacer b 0#) ≡ P.spacer (a + b) 0#
gap-beside al a b rewrite ⊔-≥ (≤-refl {0#}) = refl

gap-above : ∀ al a b → P.aboveA al (P.spacer 0# a) (P.spacer 0# b) ≡ P.spacer 0# (a + b)
gap-above al a b rewrite ⊔-≥ (≤-refl {0#}) = refl

gap-atop : ∀ a b c d → P.atop (P.spacer a b) (P.spacer c d) ≡ P.spacer (a ⊔ c) (b ⊔ d)
gap-atop a b c d = refl

-- The valid layouts (non-negative frame) with `besideA al` (`aboveA al`) and the empty layout are
-- monoids, equal when the layouts are
Valid⁺ : Set
Valid⁺ = Σ (Layout S) λ l → NN (P.width l) × NN (P.height l)

besideMonoid : VAlign → Monoid 0ℓ 0ℓ
besideMonoid al = record
  { Carrier = Valid⁺ ; _≈_ = λ x y → proj₁ x ≡ proj₁ y
  ; _∙_ = λ (a , wa , ha) (b , wb , hb) → P.besideA al a b , nn+ wa wb , nn⊔ˡ ha
  ; ε = empty , ≤-refl , ≤-refl
  ; isMonoid = record
      { isSemigroup = record
          { isMagma = record { isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
                             ; ∙-cong = λ p q → cong₂ (P.besideA al) p q }
          ; assoc = λ (a , _) (b , _) (c , _) → besideA-assoc al a b c }
      ; identity = (λ (a , _ , ha) → besideA-unitˡ al a ha) , (λ (a , _ , ha) → besideA-unitʳ al a ha) } }

aboveMonoid : Align → Monoid 0ℓ 0ℓ
aboveMonoid al = record
  { Carrier = Valid⁺ ; _≈_ = λ x y → proj₁ x ≡ proj₁ y
  ; _∙_ = λ (a , wa , ha) (b , wb , hb) → P.aboveA al a b , nn⊔ˡ wa , nn+ ha hb
  ; ε = empty , ≤-refl , ≤-refl
  ; isMonoid = record
      { isSemigroup = record
          { isMagma = record { isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
                             ; ∙-cong = λ p q → cong₂ (P.aboveA al) p q }
          ; assoc = λ (a , _) (b , _) (c , _) → aboveA-assoc al a b c }
      ; identity = (λ (a , wa , _) → aboveA-unitˡ al a wa) , (λ (a , wa , _) → aboveA-unitʳ al a wa) } }
