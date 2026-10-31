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
open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning)
open ≡-Reasoning

open import Slides.Diagram.Draw
open import Slides.Diagram.Geometry
open Space Sp
import Slides.Diagram.Place Sp as P
open P using (dbl; valignOffset; alignOffset)
open import Slides.Diagram.Laws Sp using (_⊕_; Action; itemsAct; Items)

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

-- Combining: the second item list is shifted and concatenated after the first.  Items (drawings
-- and anchors) are a semigroup under `++`, componentwise, on which shifting acts by endomorphisms,
-- so `combine` is "act, then concatenate" and its associativity is one calculation.

infixr 5 _⊞_
_⊞_ : Items → Items → Items
(d , a) ⊞ (d′ , a′) = d ++ d′ , a ++ a′

private
  act : S × S → Items → Items
  act = Action.act itemsAct

  act-⊞ : ∀ p x y → act p (x ⊞ y) ≡ act p x ⊞ act p y
  act-⊞ p (d , a) (d′ , a′) = cong₂ _,_ (L.map-++ _ d d′) (L.map-++ _ a a′)

  ⊞-assoc : ∀ x y z → (x ⊞ y) ⊞ z ≡ x ⊞ (y ⊞ z)
  ⊞-assoc (d , a) (d′ , a′) (d″ , a″) = cong₂ _,_ (L.++-assoc d d′ d″) (L.++-assoc a a′ a″)

  comb : S × S → Items → S × S → Items → Items
  comb p x q y = act p x ⊞ act q y

-- `combine` is associative given the positions that make the three children agree
comb-assoc : ∀ pa pb qc ra o₁ sb sc o₂ A B C → pa ⊕ o₁ ≡ ra → pb ⊕ o₁ ≡ sb ⊕ o₂ → qc ≡ sc ⊕ o₂ →
  comb o₁ (comb pa A pb B) qc C ≡ comb ra A o₂ (comb sb B sc C)
comb-assoc pa pb qc ra o₁ sb sc o₂ A B C ea eb ec = begin
  act o₁ (act pa A ⊞ act pb B) ⊞ act qc C          ≡⟨ cong (_⊞ act qc C) (act-⊞ o₁ (act pa A) (act pb B)) ⟩
  (act o₁ (act pa A) ⊞ act o₁ (act pb B)) ⊞ act qc C
    ≡⟨ cong₂ _⊞_ (cong₂ _⊞_ (act-⊕ pa o₁ A) (act-⊕ pb o₁ B)) (cong (λ q → act q C) ec) ⟩
  (act (pa ⊕ o₁) A ⊞ act (pb ⊕ o₁) B) ⊞ act (sc ⊕ o₂) C
    ≡⟨ cong₂ _⊞_ (cong₂ _⊞_ (cong (λ q → act q A) ea) (cong (λ q → act q B) eb)) refl ⟩
  (act ra A ⊞ act (sb ⊕ o₂) B) ⊞ act (sc ⊕ o₂) C   ≡⟨ ⊞-assoc (act ra A) (act (sb ⊕ o₂) B) (act (sc ⊕ o₂) C) ⟩
  act ra A ⊞ (act (sb ⊕ o₂) B ⊞ act (sc ⊕ o₂) C)
    ≡⟨ cong (act ra A ⊞_) (cong₂ _⊞_ (sym (act-⊕ sb o₂ B)) (sym (act-⊕ sc o₂ C))) ⟩
  act ra A ⊞ (act o₂ (act sb B) ⊞ act o₂ (act sc C)) ≡⟨ cong (act ra A ⊞_) (sym (act-⊞ o₂ (act sb B) (act sc C))) ⟩
  act ra A ⊞ act o₂ (act sb B ⊞ act sc C)          ∎
  where open Action itemsAct using (act-⊕)

-- the same for layouts, whose frames are given
combine-assoc : ∀ {W W′ H H′ Wab Hab Wbc Hbc} pa pb qc ra o₁ sb sc o₂ (a b c : Layout S) →
  W ≡ W′ → H ≡ H′ → pa ⊕ o₁ ≡ ra → pb ⊕ o₁ ≡ sb ⊕ o₂ → qc ≡ sc ⊕ o₂ →
  P.combine W H o₁ (P.combine Wab Hab pa a pb b) qc c
    ≡ P.combine W′ H′ ra a o₂ (P.combine Wbc Hbc sb b sc c)
combine-assoc pa pb qc ra o₁ sb sc o₂ (mkLayout _ _ dA aA) (mkLayout _ _ dB aB) (mkLayout _ _ dC aC) refl refl ea eb ec =
  cong (λ (d , a) → mkLayout _ _ d a) (comb-assoc pa pb qc ra o₁ sb sc o₂ (dA , aA) (dB , aB) (dC , aC) ea eb ec)

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
