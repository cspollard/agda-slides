{-# OPTIONS --safe --without-K #-}

-- Laws of the one traversal `mapXY` of a drawing's scalars (`Slides.Diagram.Draw`), proved once:
-- the identity law and fusion (a pointwise equation on the three scalar maps), and naturality, which
-- is two fusions meeting in the same composite.  Changes of scalar (`mapDraw-id`, `mapDraw-∘`),
-- moving (`drawAct`), and their interaction (`shiftDraw-nat`) are each one application.

module Slides.Diagram.DrawLaws where

open import Data.Product.Base using (_,_; proj₁; proj₂)
import Data.List.Properties as ListP
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Function.Nary.NonDependent using (congₙ)

open import Slides.Diagram.Draw
open import Slides.Diagram.Syntax using (map-fuse)

module _ {S : Set} {px py pd : S → S} where

  mapXY-id : (∀ x → px x ≡ x) → (∀ y → py y ≡ y) → (∀ r → pd r ≡ r) → ∀ d → mapXY px py pd d ≡ d
  mapXY-id ex ey er (rect x y w h s)   = congₙ 4 (λ a b c d → rect a b c d s) (ex x) (ey y) (er w) (er h)
  mapXY-id ex ey er (circle x y r s)   = congₙ 3 (λ a b c → circle a b c s) (ex x) (ey y) (er r)
  mapXY-id ex ey er (ellipse x y a b s) = congₙ 4 (λ a′ b′ c d → ellipse a′ b′ c d s) (ex x) (ey y) (er a) (er b)
  mapXY-id ex ey er (poly c ps s)      =
    cong (λ qs → poly c qs s) (trans (ListP.map-cong (λ p → cong₂ _,_ (ex (proj₁ p)) (ey (proj₂ p))) ps) (ListP.map-id ps))
  mapXY-id ex ey er (line a b c d s)   = congₙ 4 (λ a′ b′ c′ d′ → line a′ b′ c′ d′ s) (ex a) (ey b) (ex c) (ey d)
  mapXY-id ex ey er (arrow a b c d s)  = congₙ 4 (λ a′ b′ c′ d′ → arrow a′ b′ c′ d′ s) (ex a) (ey b) (ex c) (ey d)
  mapXY-id ex ey er (label x y n t s)  = cong₂ (λ a b → label a b n t s) (ex x) (ey y)
  mapXY-id ex ey er (path x y d s)     = cong₂ (λ a b → path a b d s) (ex x) (ey y)

module _ {S T U : Set} {px py pd : S → T} {qx qy qd : T → U} {rx ry rd : S → U} where

  mapXY-fuse : (∀ x → qx (px x) ≡ rx x) → (∀ y → qy (py y) ≡ ry y) → (∀ r → qd (pd r) ≡ rd r) →
               ∀ d → mapXY qx qy qd (mapXY px py pd d) ≡ mapXY rx ry rd d
  mapXY-fuse ex ey er (rect x y w h s)   = congₙ 4 (λ a b c d → rect a b c d s) (ex x) (ey y) (er w) (er h)
  mapXY-fuse ex ey er (circle x y r s)   = congₙ 3 (λ a b c → circle a b c s) (ex x) (ey y) (er r)
  mapXY-fuse ex ey er (ellipse x y a b s) = congₙ 4 (λ a′ b′ c d → ellipse a′ b′ c d s) (ex x) (ey y) (er a) (er b)
  mapXY-fuse ex ey er (poly c ps s)      =
    cong (λ qs → poly c qs s) (map-fuse (λ p → cong₂ _,_ (ex (proj₁ p)) (ey (proj₂ p))) ps)
  mapXY-fuse ex ey er (line a b c d s)   = congₙ 4 (λ a′ b′ c′ d′ → line a′ b′ c′ d′ s) (ex a) (ey b) (ex c) (ey d)
  mapXY-fuse ex ey er (arrow a b c d s)  = congₙ 4 (λ a′ b′ c′ d′ → arrow a′ b′ c′ d′ s) (ex a) (ey b) (ex c) (ey d)
  mapXY-fuse ex ey er (label x y n t s)  = cong₂ (λ a b → label a b n t s) (ex x) (ey y)
  mapXY-fuse ex ey er (path x y d s)     = cong₂ (λ a b → path a b d s) (ex x) (ey y)

-- naturality: two composites of traversals agree when they agree on each scalar map
module _ {S T T′ U : Set} {px py pd : S → T} {qx qy qd : T → U} {px′ py′ pd′ : S → T′} {qx′ qy′ qd′ : T′ → U} where

  mapXY-nat : (∀ x → qx (px x) ≡ qx′ (px′ x)) → (∀ y → qy (py y) ≡ qy′ (py′ y)) → (∀ r → qd (pd r) ≡ qd′ (pd′ r)) →
              ∀ d → mapXY qx qy qd (mapXY px py pd d) ≡ mapXY qx′ qy′ qd′ (mapXY px′ py′ pd′ d)
  mapXY-nat ex ey er d = trans (mapXY-fuse ex ey er d) (sym (mapXY-fuse (λ _ → refl) (λ _ → refl) (λ _ → refl) d))
