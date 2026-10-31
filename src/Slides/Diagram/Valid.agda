{-# OPTIONS --safe --without-K #-}

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
open P using (dbl; valignOffset; alignOffset; Placement; placement)
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

-- Every unit law is one of two facts about a placement: if its frame is the child's and the child
-- sits at the origin, the empty layout on the other side vanishes (it draws nothing, so only the
-- child's `shift 0 0` remains).  Each connective supplies its frame and offsets.
placed-unitˡ : ∀ π l → Placement.frame π ≡ P.frameOf l → Placement.posB π ≡ (0# , 0#) →
               P.placed π empty l ≡ l
placed-unitˡ (placement F p q) l@(mkLayout w h ds as) eF eq =
  trans (cong₂ (λ F q → P.placed (placement F p q) empty l) eF eq) (shift-zero l)

placed-unitʳ : ∀ π l → Placement.frame π ≡ P.frameOf l → Placement.posA π ≡ (0# , 0#) →
               P.placed π l empty ≡ l
placed-unitʳ (placement F p q) l@(mkLayout w h ds as) eF eq =
  trans (cong₂ (λ F p → P.placed (placement F p q) l empty) eF eq)
    (trans (cong₂ (mkLayout w h) (ListP.++-identityʳ _) (ListP.++-identityʳ _)) (shift-zero l))

besideA-unitˡ : ∀ al a → NN (P.height a) → P.besideA al empty a ≡ a
besideA-unitˡ al a@(mkLayout w h _ _) 0≤h =
  placed-unitˡ (P.besideP al (0# , 0#) (w , h)) a (cong₂ _,_ (+-idˡ w) (⊔-≤ 0≤h))
    (cong₂ _,_ dbl-zero (trans (cong (λ H → valignOffset al H h) (⊔-≤ 0≤h)) (valign-self al h)))

besideA-unitʳ : ∀ al a → NN (P.height a) → P.besideA al a empty ≡ a
besideA-unitʳ al a@(mkLayout w h _ _) 0≤h =
  placed-unitʳ (P.besideP al (w , h) (0# , 0#)) a (cong₂ _,_ (+-idʳ w) (⊔-≥ 0≤h))
    (cong₂ _,_ refl (trans (cong (λ H → valignOffset al H h) (⊔-≥ 0≤h)) (valign-self al h)))

aboveA-unitˡ : ∀ al a → NN (P.width a) → P.aboveA al empty a ≡ a
aboveA-unitˡ al a@(mkLayout w h _ _) 0≤w =
  placed-unitˡ (P.aboveP al (0# , 0#) (w , h)) a (cong₂ _,_ (⊔-≤ 0≤w) (+-idˡ h))
    (cong₂ _,_ (trans (cong (λ W → alignOffset al W w) (⊔-≤ 0≤w)) (align-self al w)) dbl-zero)

aboveA-unitʳ : ∀ al a → NN (P.width a) → P.aboveA al a empty ≡ a
aboveA-unitʳ al a@(mkLayout w h _ _) 0≤w =
  placed-unitʳ (P.aboveP al (w , h) (0# , 0#)) a (cong₂ _,_ (⊔-≥ 0≤w) (+-idʳ h))
    (cong₂ _,_ (trans (cong (λ W → alignOffset al W w) (⊔-≥ 0≤w)) (align-self al w)) refl)

atop-unitˡ : ∀ a → NN (P.width a) → NN (P.height a) → P.atop empty a ≡ a
atop-unitˡ a@(mkLayout w h _ _) 0≤w 0≤h =
  placed-unitˡ (P.atopP (0# , 0#) (w , h)) a (cong₂ _,_ (⊔-≤ 0≤w) (⊔-≤ 0≤h))
    (cong₂ _,_ (trans (cong (_- w) (⊔-≤ 0≤w)) (sub-self w)) (trans (cong (_- h) (⊔-≤ 0≤h)) (sub-self h)))

atop-unitʳ : ∀ a → NN (P.width a) → NN (P.height a) → P.atop a empty ≡ a
atop-unitʳ a@(mkLayout w h _ _) 0≤w 0≤h =
  placed-unitʳ (P.atopP (w , h) (0# , 0#)) a (cong₂ _,_ (⊔-≥ 0≤w) (⊔-≥ 0≤h))
    (cong₂ _,_ (trans (cong (_- w) (⊔-≥ 0≤w)) (sub-self w)) (trans (cong (_- h) (⊔-≥ 0≤h)) (sub-self h)))

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

⊔-idem : ∀ x → x ⊔ x ≡ x
⊔-idem x = ⊔-≤ ≤-refl

gap-beside : ∀ al a b → P.besideA al (P.spacer a 0#) (P.spacer b 0#) ≡ P.spacer (a + b) 0#
gap-beside al a b = cong (P.spacer (a + b)) (⊔-idem 0#)

gap-above : ∀ al a b → P.aboveA al (P.spacer 0# a) (P.spacer 0# b) ≡ P.spacer 0# (a + b)
gap-above al a b = cong (λ w → P.spacer w (a + b)) (⊔-idem 0#)

gap-atop : ∀ a b c d → P.atop (P.spacer a b) (P.spacer c d) ≡ P.spacer (a ⊔ c) (b ⊔ d)
gap-atop a b c d = refl

-- The valid layouts (non-negative frame) with `besideA al` (`aboveA al`) and the empty layout are
-- monoids, equal when the layouts are
Valid⁺ : Set
Valid⁺ = Σ (Layout S) λ l → NN (P.width l) × NN (P.height l)

-- one monoid for each connective: the operation, that it keeps frames non-negative, associativity,
-- and the units (which want the frame of the layout they are applied to)
validMonoid : (op : Layout S → Layout S → Layout S) →
  (∀ a b → NN (P.width a) × NN (P.height a) → NN (P.width b) × NN (P.height b) →
           NN (P.width (op a b)) × NN (P.height (op a b))) →
  (∀ a b c → op (op a b) c ≡ op a (op b c)) →
  (∀ a → NN (P.width a) × NN (P.height a) → op empty a ≡ a) →
  (∀ a → NN (P.width a) × NN (P.height a) → op a empty ≡ a) → Monoid 0ℓ 0ℓ
validMonoid op nn assoc unitˡ unitʳ = record
  { Carrier = Valid⁺ ; _≈_ = λ x y → proj₁ x ≡ proj₁ y
  ; _∙_ = λ (a , va) (b , vb) → op a b , nn a b va vb
  ; ε = empty , ≤-refl , ≤-refl
  ; isMonoid = record
      { isSemigroup = record
          { isMagma = record { isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
                             ; ∙-cong = λ p q → cong₂ op p q }
          ; assoc = λ (a , _) (b , _) (c , _) → assoc a b c }
      ; identity = (λ (a , v) → unitˡ a v) , (λ (a , v) → unitʳ a v) } }

besideMonoid : VAlign → Monoid 0ℓ 0ℓ
besideMonoid al = validMonoid (P.besideA al)
  (λ _ _ (wa , ha) (wb , hb) → nn+ wa wb , nn⊔ˡ ha) (besideA-assoc al)
  (λ a (_ , h) → besideA-unitˡ al a h) (λ a (_ , h) → besideA-unitʳ al a h)

aboveMonoid : Align → Monoid 0ℓ 0ℓ
aboveMonoid al = validMonoid (P.aboveA al)
  (λ _ _ (wa , ha) (wb , hb) → nn⊔ˡ wa , nn+ ha hb) (aboveA-assoc al)
  (λ a (w , _) → aboveA-unitˡ al a w) (λ a (w , _) → aboveA-unitʳ al a w)
