{-# OPTIONS --safe --without-K #-}

-- `atop` is natural along maps that are not `Ops`-homomorphisms.
--
-- `Slides.Diagram.LayoutNatural` shows that layout is natural along an `IsOpsHom`, which
-- includes preserving `-` on all pairs.  The map of ℕ into ℚ (`Slides.Diagram.NatQ.ι`) is not
-- one: it preserves `-` only where the minuend is the larger (the monus is not the difference
-- otherwise), and `percentOf` only where it is exact.  But `atop` uses neither the
-- percentage nor a difference whose minuend could be smaller: it computes `(a ⊔ b) - a` and
-- `(a ⊔ b) - b`, never `a - b` for unrelated `a` and `b`, besides sums and maxima.  So the
-- weakest hypothesis under which `atop` commutes with `mapLayout h` is that `h` preserves `+`
-- and `⊔` and the two differences `(a ⊔ b) - a`, `(a ⊔ b) - b`, which is true of `ι` with no
-- condition on the layouts (`Slides.Anim.ContinuousAssembly.atop-ι`).

open import Slides.Diagram.Scalar using (Ops)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Slides.Diagram.AtopNatural {S T : Set} (O : Ops S) (P : Ops T) (h : S → T)
  (h-+ : ∀ a b → h (Ops._+_ O a b) ≡ Ops._+_ P (h a) (h b))
  (h-⊔ : ∀ a b → h (Ops._⊔_ O a b) ≡ Ops._⊔_ P (h a) (h b))
  (h-⊔-l : ∀ a b → h (Ops._-_ O (Ops._⊔_ O a b) a) ≡ Ops._-_ P (h (Ops._⊔_ O a b)) (h a))
  (h-⊔-r : ∀ a b → h (Ops._-_ O (Ops._⊔_ O a b) b) ≡ Ops._-_ P (h (Ops._⊔_ O a b)) (h b))
  where

open import Data.List using (List; []; _∷_; map; _++_)
import Data.List.Properties as LP
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Slides.Diagram.Draw
open import Slides.Diagram.Scalar using (Ops)
import Slides.Diagram.Place as Place

private
  module PS = Place O
  module PT = Place P
  module OS = Ops O
  module OT = Ops P

  map-comm : ∀ {A B C D : Set} (f′ : B → D) (g : A → B) (g′ : C → D) (f : A → C) →
             (∀ x → f′ (g x) ≡ g′ (f x)) → ∀ xs → map f′ (map g xs) ≡ map g′ (map f xs)
  map-comm f′ g g′ f eq []       = refl
  map-comm f′ g g′ f eq (x ∷ xs) = cong₂ _∷_ (eq x) (map-comm f′ g g′ f eq xs)

  cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E) {a a′ b b′ c c′ d d′} →
          a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ → f a b c d ≡ f a′ b′ c′ d′
  cong₄ f refl refl refl refl = refl

shiftDraw-natural : ∀ dx dy d → mapDraw h (PS.shiftDraw dx dy d) ≡ PT.shiftDraw (h dx) (h dy) (mapDraw h d)
shiftDraw-natural dx dy (rect x y w ht s)  = cong₂ (λ a b → rect a b (h w) (h ht) s) (h-+ x dx) (h-+ y dy)
shiftDraw-natural dx dy (circle x y r s)   = cong₂ (λ a b → circle a b (h r) s) (h-+ x dx) (h-+ y dy)
shiftDraw-natural dx dy (line a b c d s)   =
  cong₄ (λ p q r t → line p q r t s) (h-+ a dx) (h-+ b dy) (h-+ c dx) (h-+ d dy)
shiftDraw-natural dx dy (arrow a b c d s)  =
  cong₄ (λ p q r t → arrow p q r t s) (h-+ a dx) (h-+ b dy) (h-+ c dx) (h-+ d dy)
shiftDraw-natural dx dy (label x y n t s)  = cong₂ (λ a b → label a b n t s) (h-+ x dx) (h-+ y dy)

shiftAnchor-natural : ∀ dx dy a → mapAnchor h (PS.shiftAnchor dx dy a) ≡ PT.shiftAnchor (h dx) (h dy) (mapAnchor h a)
shiftAnchor-natural dx dy (n , box l tp w ht) = cong₂ (λ a b → n , box a b (h w) (h ht)) (h-+ l dx) (h-+ tp dy)

inFrame-natural : ∀ w ht dx dy d →
  mapLayout h (PS.inFrame w ht dx dy d) ≡ PT.inFrame (h w) (h ht) (h dx) (h dy) (mapLayout h d)
inFrame-natural w ht dx dy d =
  cong₂ (layout (h w) (h ht))
    (map-comm (mapDraw h) (PS.shiftDraw dx dy) (PT.shiftDraw (h dx) (h dy)) (mapDraw h) (shiftDraw-natural dx dy) (Layout.draws d))
    (map-comm (mapAnchor h) (PS.shiftAnchor dx dy) (PT.shiftAnchor (h dx) (h dy)) (mapAnchor h) (shiftAnchor-natural dx dy) (Layout.anchors d))

overlay-natural : ∀ w ht a b →
  mapLayout h (PS.overlay w ht a b) ≡ PT.overlay (h w) (h ht) (mapLayout h a) (mapLayout h b)
overlay-natural w ht a b =
  cong₂ (layout (h w) (h ht)) (LP.map-++ (mapDraw h) (Layout.draws a) (Layout.draws b))
                              (LP.map-++ (mapAnchor h) (Layout.anchors a) (Layout.anchors b))

combine-natural : ∀ w ht px py qx qy a b →
  mapLayout h (PS.combine w ht (px , py) a (qx , qy) b)
  ≡ PT.combine (h w) (h ht) (h px , h py) (mapLayout h a) (h qx , h qy) (mapLayout h b)
combine-natural w ht px py qx qy a b =
  trans (overlay-natural w ht (PS.inFrame w ht px py a) (PS.inFrame w ht qx qy b))
        (cong₂ (PT.overlay (h w) (h ht)) (inFrame-natural w ht px py a) (inFrame-natural w ht qx qy b))

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
