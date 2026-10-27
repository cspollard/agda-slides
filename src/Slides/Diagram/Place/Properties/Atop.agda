{-# OPTIONS --safe --without-K #-}

-- `atop` is natural along maps that are not `Ops`-homomorphisms.
--
-- `Slides.Diagram.Layout.Properties` shows that layout is natural along an `IsOpsHom`, which
-- includes preserving `-` on all pairs.  The map of ℕ into ℚ (`Slides.Diagram.NatQ.ι`) is not
-- one: it preserves `-` only where the minuend is the larger (the monus is not the difference
-- otherwise), and `percentOf` only where it is exact.  But `atop` uses neither the
-- percentage nor a difference whose minuend could be smaller: it computes `(a ⊔ b) - a` and
-- `(a ⊔ b) - b`, never `a - b` for unrelated `a` and `b`, besides sums and maxima.  So the
-- weakest hypothesis under which `atop` commutes with `mapLayout h` is that `h` preserves `+`
-- and `⊔` and the two differences `(a ⊔ b) - a`, `(a ⊔ b) - b`, which is true of `ι` with no
-- condition on the layouts (`Slides.Anim.Assembly.Continuous.atop-ι`).

open import Slides.Diagram.Scalar using (Ops)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Slides.Diagram.Place.Properties.Atop {S T : Set} (O : Ops S) (P : Ops T) (h : S → T)
  (h-+ : ∀ a b → h (Ops._+_ O a b) ≡ Ops._+_ P (h a) (h b))
  (h-⊔ : ∀ a b → h (Ops._⊔_ O a b) ≡ Ops._⊔_ P (h a) (h b))
  (h-⊔-l : ∀ a b → h (Ops._-_ O (Ops._⊔_ O a b) a) ≡ Ops._-_ P (h (Ops._⊔_ O a b)) (h a))
  (h-⊔-r : ∀ a b → h (Ops._-_ O (Ops._⊔_ O a b) b) ≡ Ops._-_ P (h (Ops._⊔_ O a b)) (h b))
  where

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Slides.Diagram.Draw
import Slides.Diagram.Place as Place

open import Slides.Diagram.Place.Properties.Natural O P h h-+

private
  module PS = Place O
  module PT = Place P
  module OS = Ops O

-- `atop` commutes with `mapLayout h`
atop-natural′ : ∀ a b → mapLayout h (PS.atop a b) ≡ PT.atop (mapLayout h a) (mapLayout h b)
atop-natural′ a b =
  trans (combine-natural W H (W OS.- wa) (H OS.- ha) (W OS.- wb) (H OS.- hb) a b) eq
  where
    wa = Layout.width a ; ha = Layout.height a ; wb = Layout.width b ; hb = Layout.height b
    W = wa OS.⊔ wb ; H = ha OS.⊔ hb
    eq : PT.combine (h W) (h H) (h (W OS.- wa) , h (H OS.- ha)) (mapLayout h a)
                    (h (W OS.- wb) , h (H OS.- hb)) (mapLayout h b)
         ≡ PT.atop (mapLayout h a) (mapLayout h b)
    eq rewrite h-⊔-l wa wb | h-⊔-l ha hb | h-⊔-r wa wb | h-⊔-r ha hb | h-⊔ wa wb | h-⊔ ha hb = refl
