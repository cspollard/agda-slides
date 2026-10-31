{-# OPTIONS --safe --without-K #-}

-- The frame of a plot: whatever the data, `render p` is exactly `width × height`.  This is what
-- lets a deck place a plot without knowing its content; it holds because every mark, label and
-- axis sits in a `layers` of that size, and `layers` fixes its frame.
--
-- Plot ⊂ Diagram, in meanings.  `Framed W H` is the drawings of size exactly `W × H`; closed under
-- the overlay in that frame (`_⊙ᶠ_`, the second on top) with the empty frame `unitᶠ`, and a monoid
-- up to the layout (what is drawn): as with `besideMonoid` of `Slides.Diagram.Valid`, the terms
-- `overlay W H (spacer W H) d` and `d` differ, their layouts do not.  `renderF` is `render` with its
-- frame (`size-render`) as the second component.  It is not a homomorphism on whole plots (clipping,
-- rounding to pixels and the legend depend on all the series), but for the axes and frame of one plot
-- the marks layer is: `marks-hom`, a monoid homomorphism from the series lists (`++`, `[]`) to
-- `Framed`.  The order is what makes it one: the last series is on top, so `ss ++ ts` has `ts` over `ss`.

module Slides.Plot.Laws where

open import Level using (0ℓ)
open import Algebra.Bundles using (Monoid)
open import Algebra.Morphism.Structures using (IsMonoidHomomorphism; IsMonoidMonomorphism)
open import Data.List using (List; []; _∷_; _++_; map; reverse)
import Data.List.Properties as ListP
open import Data.Bool using (Bool; true)
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (⊔-idem)
open import Data.Product.Base using (_,_; _×_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Slides.Diagram.Convenience using (Dia; layers)
open import Slides.Diagram.Draw using (Layout; mkLayout)
open import Slides.Diagram.Syntax using (overlay; spacer)
open import Slides.Scalar.Model.Nat using (natSpace)
open import Slides.Diagram.Laws natSpace using (size; size-layout)
open import Slides.Diagram.Layout natSpace using (layout)
import Slides.Diagram.Place natSpace as P
open import Slides.Plot.Mark using (Series)
open import Slides.Plot.Render using (Plot; render; panel; withRatio; marks; markDias)

size-layers : ∀ w h (ds : List (Dia ℕ)) → size (layers w h ds) ≡ (w , h)
size-layers w h []       = refl
size-layers w h (d ∷ ds) = refl

size-render : ∀ p → size (render p) ≡ (Plot.width p , Plot.height p)
size-render p = size-layers _ _ (panel true p)

-- a plot with a ratio panel is as wide as its plots and as high as both together
size-stack : ∀ up lo → size (withRatio up lo) ≡ (Plot.width up , Plot.height up + Plot.height lo)
size-stack up lo = cong₂ _,_ (⊔-idem _) refl

-- Framed drawings

Framed : ℕ → ℕ → Set
Framed W H = Σ (Dia ℕ) λ d → size d ≡ (W , H)

-- the second on top, in the same frame; the size is the declared frame, so it is `refl`
infixr 6 _⊙ᶠ_
_⊙ᶠ_ : ∀ {W H} → Framed W H → Framed W H → Framed W H
_⊙ᶠ_ {W} {H} (a , _) (b , _) = overlay W H a b , refl

unitᶠ : ∀ {W H} → Framed W H
unitᶠ {W} {H} = spacer W H , refl

-- the layout of a drawing of a known frame, in a constructor: `layout d` is `mkLayout W H …`
frame-η : ∀ {W H} (l : Layout ℕ) → (Layout.width l , Layout.height l) ≡ (W , H) → l ≡ mkLayout W H (Layout.draws l) (Layout.anchors l)
frame-η (mkLayout w h ds as) e = cong (λ p → mkLayout (proj₁ p) (proj₂ p) ds as) e

layoutF : ∀ {W H} (a : Framed W H) → layout (proj₁ a) ≡ mkLayout W H (Layout.draws (layout (proj₁ a))) (Layout.anchors (layout (proj₁ a)))
layoutF (a , s) = frame-η (layout a) (trans (size-layout a) s)

-- overlay on layouts of the frame: the drawings concatenate
ovl-η : ∀ {W H} (x y : Layout ℕ) → P.overlay W H x y ≡ mkLayout W H (Layout.draws x ++ Layout.draws y) (Layout.anchors x ++ Layout.anchors y)
ovl-η (mkLayout _ _ _ _) (mkLayout _ _ _ _) = refl

ovl-assoc : ∀ {W H} (x y z : Layout ℕ) → P.overlay W H (P.overlay W H x y) z ≡ P.overlay W H x (P.overlay W H y z)
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
framedMonoid : ℕ → ℕ → Monoid 0ℓ 0ℓ
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

-- `render` with its frame
renderF : ∀ p → Framed (Plot.width p) (Plot.height p)
renderF p = render p , size-render p

-- the marks layer, for the axes and frame of `p`, of a list of series
marksF : Bool → ∀ p → List Series → Framed (Plot.width p) (Plot.height p)
marksF xl p ss = marks xl p ss , size-layers (Plot.width p) (Plot.height p) (reverse (markDias xl p ss))

-- `layers` of a concatenation: the first list on top, so the second layer is under the first
layers-++ : ∀ W H (ds es : List (Dia ℕ)) →
  layout (layers W H (ds ++ es)) ≡ P.overlay W H (layout (layers W H es)) (layout (layers W H ds))
layers-++ W H [] es = sym (ovl-unitʳ (layers W H es , size-layers W H es))
layers-++ W H (d ∷ ds) es = trans (cong (λ l → P.overlay W H l (layout d)) (layers-++ W H ds es))
                                  (ovl-assoc (layout (layers W H es)) (layout (layers W H ds)) (layout d))

markDias-++ : ∀ xl p ss ts → markDias xl p (ss ++ ts) ≡ markDias xl p ss ++ markDias xl p ts
markDias-++ xl p ss ts = ListP.map-++ _ ss ts

-- the marks layer is a monoid homomorphism: series lists to framed drawings
marks-++ : ∀ xl p ss ts → layout (marks xl p (ss ++ ts)) ≡ P.overlay (Plot.width p) (Plot.height p) (layout (marks xl p ss)) (layout (marks xl p ts))
marks-++ xl p ss ts =
  trans (cong (λ ds → layout (layers _ _ (reverse ds))) (markDias-++ xl p ss ts))
  (trans (cong (λ ds → layout (layers _ _ ds)) (ListP.reverse-++ (markDias xl p ss) (markDias xl p ts)))
         (layers-++ _ _ (reverse (markDias xl p ts)) (reverse (markDias xl p ss))))

marks-hom : ∀ xl p → IsMonoidHomomorphism (Monoid.rawMonoid (ListP.++-monoid Series)) (Monoid.rawMonoid (framedMonoid (Plot.width p) (Plot.height p))) (marksF xl p)
marks-hom xl p = record
  { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = cong (λ ss → layout (proj₁ (marksF xl p ss))) }
      ; homo = marks-++ xl p }
  ; ε-homo = refl }
