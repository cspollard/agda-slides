{-# OPTIONS --safe --without-K #-}

-- A plot of data read from a file: the pure half (the file's csv in, a deck out).  The file is
-- read by `PlotsDataMain` (`make plot-data`, from `data/spectrum.csv`).

module Slides.Examples.PlotsData where

open import Data.List using (_∷_; []; map)
open import Data.Maybe using (just; nothing)
open import Data.Product.Base using (_,_)
open import Data.String using (String)

open import Slides.Deck.Talk using (Talk)
open import Slides.Deck.DSL
open import Slides.Plot.Csv
open import Slides.Plot.Mark
open import Slides.Plot.Render
open import Slides.Scalar.Model.Rat using (ι)

-- the first three columns are m, events and the error
spectrum : String → Plot
spectrum csv = plot 640 400 (axisSpec (ι 0) (ι 10) "m [GeV]") (axisSpec (ι 0) (ι 100) "events")
  ( series (errors (colour 4) pts) nothing
  ∷ series (scatter (colour 4) (map (λ { (x , y , _) → x , y }) pts)) (just "data")
  ∷ [] )
  where pts = xye (rows csv)

talk : String → Talk
talk csv = do
  slide (do heading 2 "Data from a file"
            diagram "from-file" 80 (render (spectrum csv)))
