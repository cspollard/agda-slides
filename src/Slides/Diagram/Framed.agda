{-# OPTIONS --safe --without-K #-}

-- Framed drawings: `Framed W H` is the diagrams of size exactly `W × H`, closed under the overlay in
-- that frame (`_⊙ᶠ_`, the second on top) with the empty frame `unitᶠ`, and a monoid up to the layout
-- (what is drawn): as with `besideMonoid` of `Slides.Diagram.Valid`, the terms `overlay W H (spacer W H) d`
-- and `d` differ, their layouts do not.  `Slides.Plot.Laws` uses it for the frame of a plot.

open import Slides.Scalar.Space using (Space)

module Slides.Diagram.Framed {S : Set} (Sp : Space S) where

open import Level using (0ℓ)
open import Algebra.Bundles using (Monoid)
open import Data.List using (_++_)
import Data.List.Properties as ListP
open import Data.Product.Base using (_,_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Slides.Diagram.Draw using (Layout; mkLayout)
open import Slides.Diagram.Syntax using (Dia; overlay; spacer)
open import Slides.Diagram.Layout Sp using (layout)
open import Slides.Diagram.Laws Sp using (size; size-layout)
import Slides.Diagram.Place Sp as P

Framed : S → S → Set
Framed W H = Σ (Dia S) λ d → size d ≡ (W , H)

-- the second on top, in the same frame; the size is the declared frame, so it is `refl`
infixr 6 _⊙ᶠ_
_⊙ᶠ_ : ∀ {W H} → Framed W H → Framed W H → Framed W H
_⊙ᶠ_ {W} {H} (a , _) (b , _) = overlay W H a b , refl

unitᶠ : ∀ {W H} → Framed W H
unitᶠ {W} {H} = spacer W H , refl

-- the layout of a drawing of a known frame, in a constructor: `layout d` is `mkLayout W H …`
frame-η : ∀ {W H} (l : Layout S) → (Layout.width l , Layout.height l) ≡ (W , H) → l ≡ mkLayout W H (Layout.draws l) (Layout.anchors l)
frame-η (mkLayout w h ds as) e = cong (λ p → mkLayout (proj₁ p) (proj₂ p) ds as) e

layoutF : ∀ {W H} (a : Framed W H) → layout (proj₁ a) ≡ mkLayout W H (Layout.draws (layout (proj₁ a))) (Layout.anchors (layout (proj₁ a)))
layoutF (a , s) = frame-η (layout a) (trans (size-layout a) s)

-- overlay on layouts of the frame: the drawings concatenate
ovl-η : ∀ {W H} (x y : Layout S) → P.overlay W H x y ≡ mkLayout W H (Layout.draws x ++ Layout.draws y) (Layout.anchors x ++ Layout.anchors y)
ovl-η (mkLayout _ _ _ _) (mkLayout _ _ _ _) = refl

ovl-assoc : ∀ {W H} (x y z : Layout S) → P.overlay W H (P.overlay W H x y) z ≡ P.overlay W H x (P.overlay W H y z)
ovl-assoc (mkLayout _ _ da aa) (mkLayout _ _ db ab) (mkLayout _ _ dc ac) =
  cong₂ (mkLayout _ _) (ListP.++-assoc da db dc) (ListP.++-assoc aa ab ac)

ovl-unitˡ : ∀ {W H} (a : Framed W H) → P.overlay W H (layout (spacer W H)) (layout (proj₁ a)) ≡ layout (proj₁ a)
ovl-unitˡ a = sym (layoutF a)

ovl-unitʳ : ∀ {W H} (a : Framed W H) → P.overlay W H (layout (proj₁ a)) (layout (spacer W H)) ≡ layout (proj₁ a)
ovl-unitʳ a with layout (proj₁ a) | layoutF a
... | mkLayout _ _ ds as | e = trans (cong₂ (mkLayout _ _) (ListP.++-identityʳ ds) (ListP.++-identityʳ as)) (sym e)

-- the layout of an overlay is the overlay of the layouts (the frame is declared)
layout-⊙ᶠ : ∀ {W H} (a b : Framed W H) → layout (proj₁ (a ⊙ᶠ b)) ≡ P.overlay W H (layout (proj₁ a)) (layout (proj₁ b))
layout-⊙ᶠ a b = refl

-- the overlay monoid of the drawings of a frame, equal when their layouts are
framedMonoid : S → S → Monoid 0ℓ 0ℓ
framedMonoid W H = record
  { Carrier = Framed W H ; _≈_ = λ x y → layout (proj₁ x) ≡ layout (proj₁ y)
  ; _∙_ = _⊙ᶠ_ ; ε = unitᶠ
  ; isMonoid = record
      { isSemigroup = record
          { isMagma = record { isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
                             ; ∙-cong = λ {x} {y} {u} {v} p q →
                                 trans (layout-⊙ᶠ x u) (trans (cong₂ (P.overlay W H) p q) (sym (layout-⊙ᶠ y v))) }
          ; assoc = λ a b c → ovl-assoc (layout (proj₁ a)) (layout (proj₁ b)) (layout (proj₁ c)) }
      ; identity = ovl-unitˡ , ovl-unitʳ } }
