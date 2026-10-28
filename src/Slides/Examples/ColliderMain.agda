-- TODO
-- unsolved metas
{-# OPTIONS --allow-unsolved-metas --guardedness #-}

-- Executable: render `Slides.Examples.Collider.collider` with reveal.js to
-- `out/collider/` (reveal.js from a CDN) or `out/collider-local/` (a local copy).
-- Build and run with `make collider` or `make collider-local REVEAL=…`.

module Slides.Examples.ColliderMain where

open import Data.Bool using (true)
open import Data.List using (List; _∷_; [])
open import Data.String using (String)
open import Data.Maybe using (just)
open import IO using (Main; run; IO)
open import Data.Unit.Polymorphic.Base using (⊤)
open import System.Environment using (getArgs)
open import IO using (_>>=_)

import Slides.Backend.Reveal as Reveal
open import Slides.Driver
-- open import Slides.Examples.Collider using (collider)
open import Slides.Examples.ColliderSlides using (collider)

theme : Reveal.Theme
theme = record Reveal.whiteTheme { stylesheets = "slides.css" ∷ "collider.css" ∷ [] }

config : Reveal.RevealConfig
config = record Reveal.defaultConfig
  { title       = "How collider physics is accelerating data science"
  ; theme       = theme
  ; transition  = "slide"
  ; slideNumber = true
  ; width       = just 1280
  ; height      = just 720
  ; scripts     = "Reveal.configure({center: false});" ∷ []
  }

build : List String → IO ⊤
build ("local" ∷ _) = writeRevealDeck "out/collider-local" (Reveal.withSource (Reveal.local "reveal/") config) collider
build _             = writeRevealDeck "out/collider"       (Reveal.withSource (Reveal.cdn "6.0.2") config) collider

main : Main
main = run (getArgs >>= build)
