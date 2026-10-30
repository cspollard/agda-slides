{-# OPTIONS --safe --without-K #-}

-- A cube for a tensor slide: Tᵢⱼₖ as a box (`Slides.Three.Solid.box`) seen from the right and
-- above, each visible face labelled with the two indices that run over it.  `make tensor`.

module Slides.Examples.Tensor where

open import Data.Bool using (true)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _∸_; _/_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (ℚᵘ; mkℚᵘ; 0ℚᵘ; -_)
open import Data.String using (String)

open import Slides.Deck.Talk using (Talk)
open import Slides.Deck.DSL hiding (box; Text)
open import Slides.Diagram.Convenience
open import Slides.Diagram.Style using (filled)
open import Slides.Trig using (fromℕ)
open import Slides.Three.Point
open import Slides.Three.View
open import Slides.Three.Solid
open import Slides.Three.Render

W H : ℕ
W = 600
H = 460

s : ℚᵘ
s = fromℕ 120

-- turned to the right and tipped forward: the front, right and top faces show
V : View
V = viewP (mkℚᵘ (+ 1) 4) (mkℚᵘ (+ 1) 5) 0ℚᵘ

cube : Solid
cube = solid (mat "#4a7bd0" "#1d3f80" 35) true (box (- s) s (- s) s (- s) s)

-- a label centred on the page position of a point of space
labelAt : Point → String → Dia ℕ
labelAt p t = place W H (proj₁ q) (proj₂ q ∸ 15)
    (tagged "middle" 20 t (filled "#1d3f80" defaultStyle))
  where q = project (W / 2) (H / 2) V p

tensor : Dia ℕ
tensor = layers W H
  ( labelAt (point 0ℚᵘ 0ℚᵘ s) "T[i, j, ·]"
  ∷ labelAt (point s 0ℚᵘ 0ℚᵘ) "T[·, j, k]"
  ∷ labelAt (point 0ℚᵘ (- s) 0ℚᵘ) "T[i, ·, k]"
  ∷ render W H (W / 2) (H / 2) V (cube ∷ []) )

demo : Talk
demo = slide (do
  heading 2 "A tensor is a cube"
  paragraph "Fixing one index of a three-index tensor leaves a matrix: one face of the cube."
  diagram "tensor" 70 tensor)
