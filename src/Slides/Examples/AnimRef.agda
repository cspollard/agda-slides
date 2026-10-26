{-# OPTIONS --safe --without-K #-}

-- A deck for checking the page player against the frames Agda computes.  Each
-- animation is followed by its frames as ordinary diagrams (`frameDiagrams`, the very
-- list the animation is shipped from, named `ref-…`); `tests/browser/anim-ref.mjs`
-- rebuilds each frame in the page from the first frame and the edits and compares it
-- with the reference.

module Slides.Examples.AnimRef where

open import Data.List using (List; []; _∷_)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Container.FreeMonad using (pure)

open import Slides.Core using (Body; Deck)
open import Slides.DSL
open import Slides.Diagram using (Diagram)
open import Slides.Diagram.Scalar using (natOps)
open import Slides.Anim.Footprint using (parI; ⊤-witness)
open import Slides.Anim.Render using (frameDiagrams)
open import Slides.Anim.Timeline using (timeline; frames)
open import Slides.Diagram.Syntax using (Dia; atop; rectangle; disc; text; named)
open import Slides.Diagram.Notation using (_∥_; _═_; ↔)
open import Slides.Diagram using (defaultStyle; filled; stroked)
open import Slides.Diagram.Expr using (Expr; exprOps; t; lit; _⊞_; _⊖_; _⊓_; pct)
import Slides.Diagram.Notation as N
open import Slides.Anim.Syntax using (Anim; Seg; tween; tweenT; units; _⨾_; _∥ᵃ_; par)
import Slides.Anim.Track as T
open import Data.Nat using (ℕ; _+_; _*_; _∸_; _⊔_) renaming (_/_ to _÷_)
open import Data.Unit using (⊤)
open import Data.Rational using (_/_)
open import Data.Integer using (+_)
open import Slides.Examples.Intro using (mover; counter)
open import Slides.Examples.PairsHero using (hero)

private
  diagrams : List Diagram → Body
  diagrams []       = pure tt
  diagrams (d ∷ ds) = do diagram d; diagrams ds

  steps : Body
  steps = do
    animate "mover" 60 100 (parI natOps mover counter ∷ [])
    diagrams (frameDiagrams "ref-mover" 60 (timeline atop (frames natOps) (parI natOps mover counter)))

  loop : Body
  loop = do
    animateLoop "hero" 100 100 (hero 7)
    diagrams (frameDiagrams "ref-hero" 100 (timeline atop (frames natOps) (hero 7)))

------------------------------------------------------------------------
-- Templates.  Each animation is written twice: as functions of the parameter (the
-- reference, whose frames are shipped as diagrams) and as templates, whose frames the
-- page computes from formulas.  They must agree on every frame.

private
  module E = N.NotationWith (exprOps {⊤})

  ease : T.Easing
  ease = T.Bezier (+ 40) (+ 0) (+ 20) (+ 100)

  orange = filled "#c96" defaultStyle
  blue  = filled "#69c" defaultStyle

-- a box sliding right along an easing
slideF slideT : Anim ℕ (Seg ℕ)
slideF = tween 6 (+ 0 / 1) (+ 120 / 1) ease (λ x → ↔ (units x) ∥ named "slider" (rectangle 40 30 orange))
slideT = tweenT 6 (+ 0 / 1) (+ 120 / 1) ease (E.↔ t ∥ named "slider" (rectangle (lit 40) (lit 30) orange))

-- the same over 60 ticks: the formulas are the same size, the edits grow with the frames
longF longT : Anim ℕ (Seg ℕ)
longF = tween 60 (+ 0 / 1) (+ 120 / 1) ease (λ x → ↔ (units x) ∥ named "slider" (rectangle 40 30 orange))
longT = tweenT 60 (+ 0 / 1) (+ 120 / 1) ease (E.↔ t ∥ named "slider" (rectangle (lit 40) (lit 30) orange))

-- a box that grows (a percentage), a circle that follows it, and a bar that shrinks to
-- nothing (a difference that bottoms out) against a cap (a maximum); two acts in a row
growF growT : Anim ℕ (Seg ℕ)
growF =
    tween 4 (+ 0 / 1) (+ 80 / 1) T.Linear
      (λ x → named "g" (rectangle (units x) (20 + (units x * 50) ÷ 100) blue) ∥ ↔ 10 ∥ disc ((units x * 25) ÷ 100) blue)
  ⨾ tween 3 (+ 80 / 1) (+ 140 / 1) T.Linear
      (λ x → named "g" (rectangle (units x ⊔ 100) (100 ∸ units x) blue) ∥ ↔ 10 ∥ text 16 "done" defaultStyle)
growT =
    tweenT 4 (+ 0 / 1) (+ 80 / 1) T.Linear
      (named "g" (rectangle t (lit 20 ⊞ pct 50 t) blue) ∥ E.↔ (lit 10) ∥ disc (pct 25 t) blue)
  ⨾ tweenT 3 (+ 80 / 1) (+ 140 / 1) T.Linear
      (named "g" (rectangle (t ⊓ lit 100) (lit 100 ⊖ t) blue) ∥ E.↔ (lit 10) ∥ text 16 "done" defaultStyle)

-- the two together, of different lengths (the segments' parameters are independent), and
-- with the shorter padded (`par`)
bothF bothT padF padT : Anim ℕ (Seg ℕ)
bothF = slideF ∥ᵃ growF
bothT = slideT ∥ᵃ growT
padF  = par natOps slideF growF
padT  = par natOps slideT growT

private
  pair : String → Anim ℕ (Seg ℕ) → Anim ℕ (Seg ℕ) → Body
  pair n f tpl = do
    animate n 60 100 (tpl ∷ [])
    diagrams (frameDiagrams ("ref-" ++ˢ n) 60 (timeline atop (frames natOps) f))

private
  steps60 : Body
  steps60 = do
    animate "elong" 60 100 (longF ∷ [])
    diagrams (frameDiagrams "ref-elong" 60 (timeline atop (frames natOps) longF))

deck : Deck
deck = do
  slide steps
  slide loop
  slide (pair "tslide" slideF slideT)
  slide (pair "tlong" longF longT)
  slide (pair "tgrow" growF growT)
  slide (pair "tboth" bothF bothT)
  slide (pair "tpad" padF padT)
  -- the 60-tick slider again, shipped as edits, for the size comparison
  slide steps60

