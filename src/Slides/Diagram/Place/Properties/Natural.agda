{-# OPTIONS --safe --without-K #-}

-- Shifting, framing and overlaying are natural along any map that preserves `+`.
--
-- Both `Slides.Diagram.Layout.Properties` (along an `IsOpsHom`) and
-- `Slides.Diagram.Place.Properties.Atop` (along maps that are not homomorphisms, like the
-- inclusion of ℕ into ℚ) need exactly these lemmas, and only `h-+` for them.

open import Slides.Diagram.Scalar using (Ops)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Slides.Diagram.Place.Properties.Natural {S T : Set} (O : Ops S) (P : Ops T) (h : S → T)
  (h-+ : ∀ a b → h (Ops._+_ O a b) ≡ Ops._+_ P (h a) (h b))
  where

open import Data.List using ([]; _∷_; map)
import Data.List.Properties as LP
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl; cong₂; trans)

open import Slides.Cong using (cong₄)
open import Slides.Diagram.Draw
import Slides.Diagram.Place as Place

private
  module PS = Place O
  module PT = Place P

  -- `map` commutes with a family of equations
  map-comm : ∀ {A B C D : Set} (f : A → C) (g : A → B) (f′ : B → D) (g′ : C → D) →
             (∀ x → f′ (g x) ≡ g′ (f x)) → ∀ xs → map f′ (map g xs) ≡ map g′ (map f xs)
  map-comm f g f′ g′ eq []       = refl
  map-comm f g f′ g′ eq (x ∷ xs) = cong₂ _∷_ (eq x) (map-comm f g f′ g′ eq xs)

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
    (map-comm (mapDraw h) (PS.shiftDraw dx dy) (mapDraw h) (PT.shiftDraw (h dx) (h dy)) (shiftDraw-natural dx dy) (Layout.draws d))
    (map-comm (mapAnchor h) (PS.shiftAnchor dx dy) (mapAnchor h) (PT.shiftAnchor (h dx) (h dy)) (shiftAnchor-natural dx dy) (Layout.anchors d))

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
