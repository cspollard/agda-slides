{-# OPTIONS --safe --without-K #-}

-- The frame of a plot: whatever the data, `render p` is exactly `width × height`.  This is what
-- lets a deck place a plot without knowing its content; it holds because every mark, label and
-- axis sits in a `layers` of that size, and `layers` fixes its frame.

module Slides.Plot.Laws where

open import Data.List using (List; []; _∷_)
open import Data.Bool using (true)
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (⊔-idem)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

open import Slides.Diagram.Convenience using (Dia; layers)
open import Slides.Scalar.Model.Nat using (natSpace)
open import Slides.Diagram.Laws natSpace using (size)
open import Slides.Plot.Render using (Plot; render; panel; withRatio)

size-layers : ∀ w h (ds : List (Dia ℕ)) → size (layers w h ds) ≡ (w , h)
size-layers w h []       = refl
size-layers w h (d ∷ ds) = refl

size-render : ∀ p → size (render p) ≡ (Plot.width p , Plot.height p)
size-render p = size-layers _ _ (panel true p)

-- a plot with a ratio panel is as wide as its plots and as high as both together
size-stack : ∀ up lo → size (withRatio up lo) ≡ (Plot.width up , Plot.height up + Plot.height lo)
size-stack up lo = cong₂ _,_ (⊔-idem _) refl
