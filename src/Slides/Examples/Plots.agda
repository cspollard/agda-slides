{-# OPTIONS --safe --without-K #-}

-- Plots: a line with a band and a reference line, a histogram with data points, a scatter with a
-- fit.  Build with `make plots`.

module Slides.Examples.Plots where

open import Data.Integer using (+_; -[1+_])
open import Data.List using (List; _∷_; []; map; upTo; zip)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product.Base using (_,_)
open import Data.Rational as ℚ using (ℚ; _+_; _-_; _*_)

open import Slides.Deck.Talk using (Talk)
open import Slides.Deck.DSL
open import Slides.Diagram.Style using (defaultStyle; dashed)
open import Slides.Plot.Data
open import Slides.Plot.Mark
open import Slides.Plot.Render
open import Slides.Scalar.Model.Rat using (ι)

private
  lorentz : ℚ → ℚ
  lorentz x = inv (ι 1 + x * x)

  xs : List ℚ
  xs = linspace 80 (ι 0 - ι 4) (ι 4)

  curve : _
  curve = graph lorentz xs

  band′ : _
  band′ = map (λ { (x , y) → x , y - decimal (+ 1) 1 * y , y + decimal (+ 1) 1 * y }) curve

peak : Plot
peak = plot 640 400 (axisSpec (ι 0 - ι 4) (ι 4) "x") (axisSpec (ι 0) (ι 1) "1 / (1 + x²)")
  ( series (band (colour 2) band′) (just "±10%")
  ∷ series (line (colour 1) curve) (just "Lorentzian")
  ∷ series (hline (dashed "6 4" (colour 3)) (decimal (+ 5) 1)) (just "half maximum")
  ∷ [] )

-- a falling spectrum in ten bins, with a data point (and its error) in each
edges : List ℚ
edges = map ι (upTo 11)

model : List ℚ
model = map (λ i → ι 90 * inv (ι 1 + ι i * decimal (+ 4) 1) ) (upTo 10)

hist : Plot
hist = plot 640 400 (axisSpec (ι 0) (ι 10) "m [GeV]") (axisSpec (ι 0) (ι 100) "events / bin")
  ( series (steps (colour 1) edges model) (just "simulation")
  ∷ series (errors (colour 4) dataPts) nothing
  ∷ series (scatter (colour 4) (map (λ { (x , y , _) → x , y }) dataPts)) (just "data")
  ∷ [] )
  where
    dataPts = map (λ i → ι i + decimal (+ 5) 1 , ι 90 * inv (ι 1 + ι i * decimal (+ 4) 1) + decimal (+ 3) 0 , ι 4) (upTo 10)

talk : Talk
talk = do
  slide (do heading 2 "A line with a band"
            diagram "peak" 80 (render peak))
  slide (do heading 2 "A histogram with data"
            diagram "hist" 80 (render hist))
