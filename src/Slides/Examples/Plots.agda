{-# OPTIONS --safe --without-K #-}

-- Plots: a line with a band and a reference line, a histogram with data points, a scatter with a
-- fit.  Build with `make plots`.

module Slides.Examples.Plots where

open import Data.Integer using (+_; -[1+_])
open import Data.List using (List; _∷_; []; map; upTo; zip)
open import Data.Maybe using (just; nothing)
open import Data.Nat as ℕ using (ℕ)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; _+_; _-_; _*_)

open import Slides.Deck.Talk using (Talk)
open import Slides.Deck.DSL
open import Slides.Diagram.Style using (defaultStyle; dashed)
open import Slides.Deck.Anim using (Linear)
open import Slides.Plot.Anim
open import Slides.Plot.Data
open import Slides.Plot.Mark
open import Slides.Plot.Render
open import Slides.Scalar.Model.Rat using (ι)

-- a Lorentzian of curvature `w` with a ±10% band and its half maximum
peakW : ℚ → Plot
peakW w = plot 640 400 (axisSpec (ι 0 - ι 4) (ι 4) "x") (axisSpec (ι 0) (ι 1) "1 / (1 + w x²)")
  ( series (band (colour 2) (map (λ { (x , y) → x , y - tenth * y , y + tenth * y }) curve)) (just "±10%")
  ∷ series (line (colour 1) curve) (just "Lorentzian")
  ∷ series (hline (dashed "6 4" (colour 3)) (decimal (+ 5) 1)) (just "half maximum")
  ∷ [] )
  where tenth = decimal (+ 1) 1
        curve = graph (λ x → inv (ι 1 + w * x * x)) (linspace 80 (ι 0 - ι 4) (ι 4))

peak : Plot
peak = peakW (ι 1)

-- a falling spectrum in ten bins, with a data point (and its error) in each
edges : List ℚ
edges = map ι (upTo 11)

model : List ℚ
model = map (λ i → ι 90 * inv (ι 1 + ι i * decimal (+ 4) 1) ) (upTo 10)

dataPts : List (ℚ × ℚ × ℚ)
dataPts = map (λ i → ι i + decimal (+ 5) 1 , ι 90 * inv (ι 1 + ι i * decimal (+ 4) 1) + decimal (+ 3) 0 , ι 4) (upTo 10)

hist : Plot
hist = plot 640 400 (axisSpec (ι 0) (ι 10) "m [GeV]") (axisSpec (ι 0) (ι 100) "events / bin")
  ( series (steps (colour 1) edges model) (just "simulation")
  ∷ series (errors (colour 4) dataPts) nothing
  ∷ series (scatter (colour 4) (map (λ { (x , y , _) → x , y }) dataPts)) (just "data")
  ∷ [] )

-- under it, data over simulation per bin, sharing the x axis; the upper panel has no x labels
ratios : List (ℚ × ℚ × ℚ)
ratios = map (λ { ((x , y , e) , m) → x , y * inv m , e * inv m }) (zip dataPts model)

ratio : Plot
ratio = plot 640 220 (axisSpec (ι 0) (ι 10) "m [GeV]") (axisSpec (decimal (+ 5) 1) (decimal (+ 15) 1) "data / sim")
  ( series (hline (dashed "6 4" (colour 3)) (ι 1)) nothing
  ∷ series (errors (colour 4) ratios) nothing
  ∷ series (scatter (colour 4) (map (λ { (x , y , _) → x , y }) ratios)) nothing
  ∷ [] )

-- a power law over three decades, on a log axis
power : Plot
power = plot 640 400 (axisSpec (ι 0) (ι 10) "x") (logAxis (ι 1) (ι 1000) "1000 / x²")
  ( series (line (colour 1) (graph (λ x → ι 1000 * inv (x * x)) (linspace 60 (ι 1) (ι 10)))) (just "model")
  ∷ series (scatter (colour 5) (map (λ i → ι i , ι 1000 * inv (ι i * ι i) * decimal (+ 11) 1) (map ℕ.suc (upTo 9)))) (just "data")
  ∷ [] )

-- the same Lorentzian as one exact function: a smooth curve, cut where it leaves the box
smooth : Plot
smooth = plot 640 400 (axisSpec (ι 0 - ι 4) (ι 4) "x") (axisSpec (ι 0) (ι 1) "1 / (1 + x²)")
  ( series (exact (colour 1) (λ x → inv (ι 1 + x * x))) (just "exact")
  ∷ series (line (dashed "6 4" (colour 3)) (graph (λ x → inv (ι 1 + x * x)) (linspace 8 (ι 0 - ι 4) (ι 4)))) (just "9 samples")
  ∷ [] )

talk : Talk
talk = do
  slide (do heading 2 "A line with a band"
            diagram "peak" 80 (render peak))
  slide (do heading 2 "A histogram with data"
            diagram "hist" 80 (render hist))
  slide (do heading 2 "A ratio panel"
            diagram "ratio" 80 (withRatio (record hist { height = 280 }) ratio))
  slide (do heading 2 "A smooth curve from a function"
            diagram "smooth" 80 (render smooth))
  slide (do heading 2 "A log axis"
            diagram "power" 80 (render power))
  slide (do heading 2 "Series, one at a time"
            animate "reveal" 80 400 (reveal peak))
  slide (do heading 2 "Morphing the data"
            animate "morph" 80 60 (morph 16 Linear peak (peakW (ι 4)) ∷ []))
