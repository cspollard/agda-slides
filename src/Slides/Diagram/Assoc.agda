{-# OPTIONS --safe --without-K #-}

-- Associativity of the stacking connectives: `besideA al` and `aboveA al` are associative as
-- layouts (frame, drawings and anchors, in order), for every alignment (`besideA-assoc`,
-- `aboveA-assoc`).
--
--   (a ∥ b) ∥ c   ≡   a ∥ (b ∥ c)          (a ═ b) ═ c   ≡   a ═ (b ═ c)
--
-- Both groupings put `a`, `b`, `c` at the same positions: a child's position is a sum of an
-- inner and an outer alignment offset, and the sums agree because exact subtraction composes,
-- `(y - x) + (z - y) ≡ z - x` for `x ≤ y ≤ z` (`sub-trans`).  One generic statement about
-- shifted lists (`Shapes.assoc-shape`) serves drawings and anchors.  For `atop`: `Commute`.

open import Slides.Scalar.Space using (Space)

module Slides.Diagram.Assoc {S : Set} (Sp : Space S) where

open import Data.List using (List; []; _∷_; map; _++_)
import Data.List.Properties as L
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Slides.Diagram.Draw
open import Slides.Diagram.Geometry
open Space Sp
import Slides.Diagram.Place Sp as P
open P using (dbl; valignOffset; alignOffset)
open import Slides.Diagram.Laws Sp using (shiftDraw-shift; shiftAnchor-shift; map-map)

-- Arithmetic

dbl-+ : ∀ a b → dbl a + dbl b ≡ dbl (a + b)
dbl-+ a b = +-interchange a a b b

-- the alignment offsets compose along `x ≤ y ≤ z`, like the differences they are made of
valign-trans : ∀ al {x y z} → x ≤ y → y ≤ z → valignOffset al y x + valignOffset al z y ≡ valignOffset al z x
valign-trans top    _ _   = +-idˡ 0#
valign-trans middle p q   = sub-trans p q
valign-trans bottom p q   = trans (dbl-+ _ _) (cong dbl (sub-trans p q))

align-trans : ∀ al {x y z} → x ≤ y → y ≤ z → alignOffset al y x + alignOffset al z y ≡ alignOffset al z x
align-trans left    _ _   = +-idˡ 0#
align-trans centred p q   = sub-trans p q
align-trans right   p q   = trans (dbl-+ _ _) (cong dbl (sub-trans p q))

-- Shifted lists

infixl 6 _⊕_
_⊕_ : S × S → S × S → S × S
p ⊕ o = proj₁ p + proj₁ o , proj₂ p + proj₂ o

-- for anything that shifts (drawings, anchors): shifting by `p` then `o` is shifting by `p ⊕ o`
module Shapes {X : Set} (sh : S × S → X → X) (sh-sh : ∀ p o x → sh o (sh p x) ≡ sh (p ⊕ o) x) where

  shifted : ∀ p o r → p ⊕ o ≡ r → ∀ ds → map (sh o) (map (sh p) ds) ≡ map (sh r) ds
  shifted p o r e ds = trans (map-map (sh o) (sh p) (sh (p ⊕ o)) (sh-sh p o) ds) (cong (λ q → map (sh q) ds) e)

  -- three lists, grouped left (`a` and `b` inside, shifted by `o₁` outside, `c` beside) or
  -- right (`b` and `c` inside, shifted by `o₂`), with the positions that make them agree
  assoc-shape : ∀ pa pb qc ra o₁ sb sc o₂ (dA dB dC : List X) →
    pa ⊕ o₁ ≡ ra → pb ⊕ o₁ ≡ sb ⊕ o₂ → qc ≡ sc ⊕ o₂ →
    map (sh o₁) (map (sh pa) dA ++ map (sh pb) dB) ++ map (sh qc) dC
      ≡ map (sh ra) dA ++ map (sh o₂) (map (sh sb) dB ++ map (sh sc) dC)
  assoc-shape pa pb qc ra o₁ sb sc o₂ dA dB dC ea eb ec =
    trans (cong (_++ map (sh qc) dC) (L.map-++ (sh o₁) (map (sh pa) dA) (map (sh pb) dB)))
     (trans (cong₂ _++_ (cong₂ _++_ (shifted pa o₁ ra ea dA) (trans (shifted pb o₁ (pb ⊕ o₁) refl dB) (trans (cong (λ q → map (sh q) dB) eb) (sym (shifted sb o₂ (sb ⊕ o₂) refl dB))))) (cong (λ q → map (sh q) dC) ec))
       (trans (L.++-assoc (map (sh ra) dA) (map (sh o₂) (map (sh sb) dB)) (map (sh (sc ⊕ o₂)) dC))
         (cong (map (sh ra) dA ++_)
           (trans (cong (map (sh o₂) (map (sh sb) dB) ++_) (sym (shifted sc o₂ (sc ⊕ o₂) refl dC)))
                  (sym (L.map-++ (sh o₂) (map (sh sb) dB) (map (sh sc) dC)))))))

private
  module D = Shapes (λ p → P.shiftDraw (proj₁ p) (proj₂ p))
                    (λ p o x → shiftDraw-shift (proj₁ o) (proj₂ o) (proj₁ p) (proj₂ p) x)
  module N = Shapes (λ p → P.shiftAnchor (proj₁ p) (proj₂ p))
                    (λ p o x → shiftAnchor-shift (proj₁ o) (proj₂ o) (proj₁ p) (proj₂ p) x)

-- `combine` is associative given the positions that make the three children agree
combine-assoc : ∀ {W W′ H H′ Wab Hab Wbc Hbc} pa pb qc ra o₁ sb sc o₂ (a b c : Layout S) →
  W ≡ W′ → H ≡ H′ → pa ⊕ o₁ ≡ ra → pb ⊕ o₁ ≡ sb ⊕ o₂ → qc ≡ sc ⊕ o₂ →
  P.combine W H o₁ (P.combine Wab Hab pa a pb b) qc c
    ≡ P.combine W′ H′ ra a o₂ (P.combine Wbc Hbc sb b sc c)
combine-assoc pa pb qc ra o₁ sb sc o₂ (mkLayout _ _ dA aA) (mkLayout _ _ dB aB) (mkLayout _ _ dC aC) refl refl ea eb ec =
  cong₂ (mkLayout _ _) (D.assoc-shape pa pb qc ra o₁ sb sc o₂ dA dB dC ea eb ec)
                       (N.assoc-shape pa pb qc ra o₁ sb sc o₂ aA aB aC ea eb ec)

besideA-assoc : ∀ al a b c → P.besideA al (P.besideA al a b) c ≡ P.besideA al a (P.besideA al b c)
besideA-assoc al a@(mkLayout wa ha _ _) b@(mkLayout wb hb _ _) c@(mkLayout wc hc _ _) =
  combine-assoc {Wab = wa + wb} {Hab = ha ⊔ hb} {Wbc = wb + wc} {Hbc = hb ⊔ hc}
    (0# , valignOffset al (ha ⊔ hb) ha) (dbl wa , valignOffset al (ha ⊔ hb) hb)
    (dbl (wa + wb) , valignOffset al ((ha ⊔ hb) ⊔ hc) hc) (0# , valignOffset al (ha ⊔ (hb ⊔ hc)) ha)
    (0# , valignOffset al ((ha ⊔ hb) ⊔ hc) (ha ⊔ hb))
    (0# , valignOffset al (hb ⊔ hc) hb) (dbl wb , valignOffset al (hb ⊔ hc) hc)
    (dbl wa , valignOffset al (ha ⊔ (hb ⊔ hc)) (hb ⊔ hc)) a b c
    (+-assoc wa wb wc) (⊔-assoc ha hb hc)
    (cong₂ _,_ (+-idˡ 0#) (trans (valign-trans al (⊔-ub₁ ha hb) (⊔-ub₁ (ha ⊔ hb) hc)) (cong (λ z → valignOffset al z ha) (⊔-assoc ha hb hc))))
    (cong₂ _,_ (trans (+-idʳ _) (sym (+-idˡ _)))
       (trans (valign-trans al (⊔-ub₂ ha hb) (⊔-ub₁ (ha ⊔ hb) hc))
         (trans (cong (λ z → valignOffset al z hb) (⊔-assoc ha hb hc))
                (sym (valign-trans al (⊔-ub₁ hb hc) (⊔-ub₂ ha (hb ⊔ hc)))))))
    (cong₂ _,_ (sym (trans (dbl-+ wb wa) (cong dbl (+-comm wb wa))))
       (trans (cong (λ z → valignOffset al z hc) (⊔-assoc ha hb hc))
              (sym (valign-trans al (⊔-ub₂ hb hc) (⊔-ub₂ ha (hb ⊔ hc))))))

aboveA-assoc : ∀ al a b c → P.aboveA al (P.aboveA al a b) c ≡ P.aboveA al a (P.aboveA al b c)
aboveA-assoc al a@(mkLayout wa ha _ _) b@(mkLayout wb hb _ _) c@(mkLayout wc hc _ _) =
  combine-assoc {Wab = wa ⊔ wb} {Hab = ha + hb} {Wbc = wb ⊔ wc} {Hbc = hb + hc}
    (alignOffset al (wa ⊔ wb) wa , 0#) (alignOffset al (wa ⊔ wb) wb , dbl ha)
    (alignOffset al ((wa ⊔ wb) ⊔ wc) wc , dbl (ha + hb)) (alignOffset al (wa ⊔ (wb ⊔ wc)) wa , 0#)
    (alignOffset al ((wa ⊔ wb) ⊔ wc) (wa ⊔ wb) , 0#)
    (alignOffset al (wb ⊔ wc) wb , 0#) (alignOffset al (wb ⊔ wc) wc , dbl hb)
    (alignOffset al (wa ⊔ (wb ⊔ wc)) (wb ⊔ wc) , dbl ha) a b c
    (⊔-assoc wa wb wc) (+-assoc ha hb hc)
    (cong₂ _,_ (trans (align-trans al (⊔-ub₁ wa wb) (⊔-ub₁ (wa ⊔ wb) wc)) (cong (λ z → alignOffset al z wa) (⊔-assoc wa wb wc))) (+-idˡ 0#))
    (cong₂ _,_
       (trans (align-trans al (⊔-ub₂ wa wb) (⊔-ub₁ (wa ⊔ wb) wc))
         (trans (cong (λ z → alignOffset al z wb) (⊔-assoc wa wb wc))
                (sym (align-trans al (⊔-ub₁ wb wc) (⊔-ub₂ wa (wb ⊔ wc))))))
       (trans (+-idʳ _) (sym (+-idˡ _))))
    (cong₂ _,_
       (trans (cong (λ z → alignOffset al z wc) (⊔-assoc wa wb wc))
              (sym (align-trans al (⊔-ub₂ wb wc) (⊔-ub₂ wa (wb ⊔ wc)))))
       (sym (trans (dbl-+ hb ha) (cong dbl (+-comm hb ha)))))

-- the same for diagrams: a grouping of stacked children does not change the layout
import Slides.Diagram.Syntax as D
open import Slides.Diagram.Layout Sp using (layout)

layout-besideA-assoc : ∀ al (a b c : D.Dia S) →
  layout (D.besideA al (D.besideA al a b) c) ≡ layout (D.besideA al a (D.besideA al b c))
layout-besideA-assoc al a b c = besideA-assoc al (layout a) (layout b) (layout c)

layout-aboveA-assoc : ∀ al (a b c : D.Dia S) →
  layout (D.aboveA al (D.aboveA al a b) c) ≡ layout (D.aboveA al a (D.aboveA al b c))
layout-aboveA-assoc al a b c = aboveA-assoc al (layout a) (layout b) (layout c)
