{-# OPTIONS --safe --without-K #-}

-- `atop` and the overlay of layouts: associative, and commutative up to a permutation.
--
--   atop (atop a b) c ≡ atop a (atop b c)              (`atop-assoc`; on the nose)
--   atop a b ≈ᵖ atop b a                               (`atop-comm`)
--   ovl a b ≈ᵖ ovl b a                                 (`ovl-comm`, the overlay of `Par`)
--
-- where `l ≈ᵖ m` says the frames are equal and the drawings (anchors) are the same up to order:
-- the same picture, stacked the other way round.  `atop` centres both children in the join of
-- their frames, so positions agree by `sub-trans` (as in `Assoc`) and the offsets of `a b` and
-- `b a` coincide, `⊔` being commutative; no hypothesis on sizes.  `atop a b ≡ atop b a` is false
-- in general: the order of the drawings is the stacking order.

open import Slides.Scalar.Space using (Space)

module Slides.Diagram.Commute {S : Set} (Sp : Space S) where

open import Data.List using (map)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as ↭P
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Slides.Diagram.Draw
open Space Sp
import Slides.Diagram.Place Sp as P
open import Slides.Diagram.Laws Sp using (ovl)
open import Slides.Diagram.Assoc Sp using (combine-assoc)

-- the same frame, the same things drawn and named
_≈ᵖ_ : Layout S → Layout S → Set
l ≈ᵖ m = P.width l ≡ P.width m × P.height l ≡ P.height m ×
         Layout.draws l ↭ Layout.draws m × Layout.anchors l ↭ Layout.anchors m

private
  st : ∀ {x y z z′} → x ≤ y → y ≤ z → z ≡ z′ → (y - x) + (z - y) ≡ z′ - x
  st p q e = trans (sub-trans p q) (cong (_- _) e)

atop-assoc : ∀ a b c → P.atop (P.atop a b) c ≡ P.atop a (P.atop b c)
atop-assoc a@(mkLayout wa ha _ _) b@(mkLayout wb hb _ _) c@(mkLayout wc hc _ _) =
  combine-assoc {Wab = wa ⊔ wb} {Hab = ha ⊔ hb} {Wbc = wb ⊔ wc} {Hbc = hb ⊔ hc}
    (wab - wa , hab - ha) (wab - wb , hab - hb) (W - wc , H - hc) (W′ - wa , H′ - ha)
    (W - wab , H - hab) (wbc - wb , hbc - hb) (wbc - wc , hbc - hc) (W′ - wbc , H′ - hbc) a b c
    (⊔-assoc wa wb wc) (⊔-assoc ha hb hc)
    (cong₂ _,_ (st (⊔-ub₁ wa wb) (⊔-ub₁ _ wc) (⊔-assoc wa wb wc)) (st (⊔-ub₁ ha hb) (⊔-ub₁ _ hc) (⊔-assoc ha hb hc)))
    (cong₂ _,_
       (trans (st (⊔-ub₂ wa wb) (⊔-ub₁ _ wc) (⊔-assoc wa wb wc)) (sym (st (⊔-ub₁ wb wc) (⊔-ub₂ wa _) refl)))
       (trans (st (⊔-ub₂ ha hb) (⊔-ub₁ _ hc) (⊔-assoc ha hb hc)) (sym (st (⊔-ub₁ hb hc) (⊔-ub₂ ha _) refl))))
    (cong₂ _,_
       (trans (cong (_- wc) (⊔-assoc wa wb wc)) (sym (st (⊔-ub₂ wb wc) (⊔-ub₂ wa _) refl)))
       (trans (cong (_- hc) (⊔-assoc ha hb hc)) (sym (st (⊔-ub₂ hb hc) (⊔-ub₂ ha _) refl))))
  where
    wab = wa ⊔ wb ; hab = ha ⊔ hb ; wbc = wb ⊔ wc ; hbc = hb ⊔ hc
    W = wab ⊔ wc ; H = hab ⊔ hc ; W′ = wa ⊔ wbc ; H′ = ha ⊔ hbc

atop-comm : ∀ a b → P.atop a b ≈ᵖ P.atop b a
atop-comm (mkLayout wa ha da aa) (mkLayout wb hb db ab)
  rewrite ⊔-comm wb wa | ⊔-comm hb ha =
  refl , refl , ↭P.++-comm (map _ da) (map _ db) , ↭P.++-comm (map _ aa) (map _ ab)

ovl-comm : ∀ a b → ovl a b ≈ᵖ ovl b a
ovl-comm (mkLayout wa ha da aa) (mkLayout wb hb db ab)
  rewrite ⊔-comm wb wa | ⊔-comm hb ha = refl , refl , ↭P.++-comm da db , ↭P.++-comm aa ab
