{-# OPTIONS --safe --without-K #-}

-- The frame of a plot: whatever the data, `render p` is exactly `width × height`.  This is what
-- lets a deck place a plot without knowing its content; it holds because every mark, label and
-- axis sits in a `layers` of that size, and `layers` fixes its frame.
--
-- Plot ⊂ Diagram, in meanings: `Framed W H` (`Slides.Diagram.Framed`) is the drawings of size exactly
-- `W × H`, a monoid under the overlay up to the layout.  `renderF` is `render` with its
-- frame (`size-render`) as the second component.  It is not a homomorphism on whole plots (clipping,
-- rounding to pixels and the legend depend on all the series), but for the axes and frame of one plot
-- the marks layer is: `marks-hom`, a monoid homomorphism from the series lists (`++`, `[]`) to
-- `Framed`.  The order is what makes it one: the last series is on top, so `ss ++ ts` has `ts` over `ss`.

module Slides.Plot.Laws where

open import Algebra.Bundles using (Monoid)
open import Algebra.Morphism.Structures using (IsMonoidHomomorphism; IsMonoidMonomorphism)
open import Data.List using (List; []; _∷_; _++_; map; reverse)
import Data.List.Properties as ListP
open import Data.Bool using (Bool; true)
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (⊔-idem)
open import Data.Product.Base using (_,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Slides.Diagram.Convenience using (Dia; layers)
open import Slides.Scalar.Model.Nat using (natSpace)
open import Slides.Diagram.Laws natSpace using (size)
open import Slides.Diagram.Framed natSpace
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
