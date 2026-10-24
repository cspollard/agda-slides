{-# OPTIONS --safe --without-K #-}

-- HTML rendering of the `Placed` capability (reveal.js and plain backends).
--
-- A placed box is a `<div class="placed">` with percentage coordinates; the
-- stylesheets position it with `position: fixed`, whose containing block is
-- the slide canvas (reveal.js scales the canvas with a transform; the plain
-- backend's slide fills the window).

module Slides.Backend.Placed where

open import Data.Bool using (Bool; true; false)
open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.Product using (_,_)
open import Data.String using (String) renaming (_++_ to _++ˢ_)

open import Slides.Capability.Placed
open import Slides.Backend.HTML
open import Slides.Backend.Common

private
  pct : String → ℕ → String
  pct name n = name ++ˢ ":" ++ˢ show n ++ˢ "%;"

  cls : Bool → String
  cls false = "placed"
  cls true  = "placed fragment"

instance
  htmlcap-Placed : HTMLCap Placed
  htmlcap-Placed = record
    { render = λ { (place later x y w h c) →
        hElement "div"
          ( ("class" , cls later)
          ∷ ("style" , pct "left" x ++ˢ pct "top" y ++ˢ pct "width" w ++ˢ pct "height" h)
          ∷ [])
          (renderContentProgram c)
        ∷ [] } }
