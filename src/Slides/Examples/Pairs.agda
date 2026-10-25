{-# OPTIONS --safe --without-K #-}

-- An introduction to "It Just Takes Two: Scaling Amortized Inference to Large
-- Sets" (Wehenkel, Kagan, Heinrich, Pollard; arXiv:2605.07972) in eleven
-- slides.  It uses typed math, SVG diagrams, cards and callouts styled by
-- `assets/pairs/pairs.css`, and the animations of `assets/pairs/pairs.js`
-- (point pairs, pulses along arrows, a live histogram, growing bars and
-- counters).  See `docs/PairsDeck.md`.

module Slides.Examples.Pairs where

open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ)
open import Data.String using (String) renaming (_++_ to _++ˢ_)

open import Slides.Core using (Deck; emph; strong; inlineMath; link; codeSpan)
open import Slides.DSL
open import Slides.Diagram
import Slides.Math as M

------------------------------------------------------------------------
-- Mathematics

θ ψ X N x₁ : M.Math
θ  = M.greek M.theta
ψ  = M.greek M.psi
X  = M.var "X"
N  = M.var "N"
x₁ = M.idx "x" "i"

-- p(…)
p : List M.Math → M.Math
p = M.call (M.var "p")

-- p(θ, X) = p(θ) ∫ p(ψ) ∏ᵢ p(xᵢ | θ, ψ) dψ
joint : M.Math
joint =
  M.rel M.eq (p (θ ∷ X ∷ []))
    (M.juxt (p (θ ∷ []))
       (M.integral (M.greek M.Psi) (M.var "")
          (M.juxt (p (ψ ∷ []))
             (M.juxt (M.prod (M.rel M.eq "i" 1) N (p (M.rel M.mid x₁ (M.tuple (θ ∷ ψ ∷ [])) ∷ [])))
                     (M.dd ψ)))))

-- T_ω(X) = (1/N) ∑ᵢ t_ω(xᵢ)
meanPool : M.Math
meanPool =
  M.rel M.eq (M.call (M.idx (M.var "T") (M.greek M.omega)) (X ∷ []))
    (M.juxt (M.frac 1 N)
       (M.sum (M.rel M.eq "i" 1) N (M.call (M.idx (M.var "t") (M.greek M.omega)) (x₁ ∷ []))))

-- g(y₁) + g(y₂) = h(y₁ + y₂)
cauchy : M.Math
cauchy =
  M.rel M.eq (M.call "g" (M.idx "y" 1 ∷ []) M.+ M.call "g" (M.idx "y" 2 ∷ []))
             (M.call "h" (M.idx "y" 1 M.+ M.idx "y" 2 ∷ []))

------------------------------------------------------------------------
-- Diagram vocabulary: every look comes from a CSS class

cls : String → Style
cls c = withClass c defaultStyle

-- a rounded card; the id lets scripts light it up
card : String → String → ℕ → ℕ → ℕ → ℕ → Element
card i c x y w h = rect x y w h (rounded 18 (withId i (withClass c defaultStyle)))

boxEl : ℕ → ℕ → ℕ → ℕ → String → Element
boxEl x y w h c = rect x y w h (rounded 14 (cls c))

txt : ℕ → ℕ → ℕ → String → Element
txt x y s t = label x y s t defaultStyle

dim : ℕ → ℕ → ℕ → String → Element
dim x y s t = label x y s t (cls "dim")

big : ℕ → ℕ → ℕ → String → Element
big x y s t = label x y s t (cls "big")

-- an arrow that pulses travel along
flow : ℕ → ℕ → ℕ → ℕ → String → Element
flow a b c d col = arrow a b c d (cls ("flow " ++ˢ col))

------------------------------------------------------------------------
-- Slide 2: the problem

problem : Diagram
problem = record
  { name = "d-problem" ; width = 520 ; height = 400 ; percent = 100
  ; elements =
      dim 160 14 16 "parameter of interest"
    ∷ dim 370 14 16 "shared nuisance"
    ∷ circle 160 66 36 (withClass "node blue" defaultStyle)
    ∷ big 160 66 30 "θ"
    ∷ circle 370 66 36 (withClass "node crimson" defaultStyle)
    ∷ big 370 66 30 "ψ"
    ∷ flow 150 100 62 270 "cy"
    ∷ flow 160 102 182 270 "cy"
    ∷ flow 170 100 300 270 "cy"
    ∷ flow 180 98 424 270 "cy"
    ∷ flow 360 102 70 270 "am"
    ∷ flow 366 102 190 270 "am"
    ∷ flow 372 102 310 270 "am"
    ∷ flow 380 98 430 270 "am"
    ∷ boxEl 12 274 100 54 "node"
    ∷ txt 62 301 22 "x₁"
    ∷ boxEl 132 274 100 54 "node"
    ∷ txt 182 301 22 "x₂"
    ∷ boxEl 252 274 100 54 "node"
    ∷ txt 302 301 22 "x₃"
    ∷ boxEl 372 274 100 54 "node"
    ∷ txt 422 301 22 "x_N"
    ∷ dim 260 372 18 "one set X = {x₁, …, x_N} sharing the same ψ"
    ∷ [] }

------------------------------------------------------------------------
-- Slide 5: the building blocks

pipeline : Diagram
pipeline = record
  { name = "d-pipeline" ; width = 1000 ; height = 290 ; percent = 100
  ; elements =
      boxEl 10 30 80 50 "node" ∷ txt 50 55 20 "x₁"
    ∷ boxEl 10 120 80 50 "node" ∷ txt 50 145 20 "x₂"
    ∷ boxEl 10 210 80 50 "node" ∷ txt 50 235 20 "x_N"
    ∷ flow 90 55 190 55 "cy" ∷ flow 90 145 190 145 "cy" ∷ flow 90 235 190 235 "cy"
    ∷ boxEl 190 30 100 50 "node blue" ∷ txt 240 55 20 "t_ω"
    ∷ boxEl 190 120 100 50 "node blue" ∷ txt 240 145 20 "t_ω"
    ∷ boxEl 190 210 100 50 "node blue" ∷ txt 240 235 20 "t_ω"
    ∷ flow 290 55 460 135 "cy" ∷ flow 290 145 458 145 "cy" ∷ flow 290 235 460 155 "cy"
    ∷ circle 500 145 42 (cls "node crimson")
    ∷ big 500 145 20 "mean"
    ∷ flow 542 145 610 145 "am"
    ∷ boxEl 610 112 130 66 "node on"
    ∷ txt 675 145 22 "T_ω(X)"
    ∷ flow 740 145 800 145 "am"
    ∷ boxEl 800 112 190 66 "node plum"
    ∷ txt 895 135 22 "q_φ"
    ∷ dim 895 160 15 "posterior over θ"
    ∷ txt 895 24 20 "N"
    ∷ flow 895 40 895 108 "am"
    ∷ dim 50 275 15 "set elements"
    ∷ dim 240 275 15 "same network"
    ∷ dim 500 205 15 "any set size"
    ∷ [] }

------------------------------------------------------------------------
-- Slide 6: PAIRS

stages : Diagram
stages = record
  { name = "d-stages" ; width = 1100 ; height = 250 ; percent = 100
  ; elements =
      card "st1" "node" 10 20 330 200
    ∷ big 175 62 28 "1  Pretrain"
    ∷ txt 175 112 22 "train (ω, φ) jointly"
    ∷ txt 175 146 22 "on sets of size 1 and 2"
    ∷ dim 175 190 17 "cheap: tiny sets"
    ∷ flow 340 120 385 120 "am"
    ∷ card "st2" "node" 385 20 330 200
    ∷ big 550 62 28 "2  Cache"
    ∷ txt 550 112 22 "freeze t_ω, embed every set"
    ∷ txt 550 146 22 "store the mean T̄ once"
    ∷ dim 550 190 17 "one pass, parallel"
    ∷ flow 715 120 760 120 "am"
    ∷ card "st3" "node" 760 20 330 200
    ∷ big 925 62 28 "3  Finetune"
    ∷ txt 925 112 22 "update the head φ only"
    ∷ txt 925 146 22 "on cached T̄, any N"
    ∷ dim 925 190 17 "cost ≈ independent of N"
    ∷ [] }

------------------------------------------------------------------------
-- Slide 7: why pairs are enough

chain : Diagram
chain = record
  { name = "d-chain" ; width = 1100 ; height = 190 ; percent = 100
  ; elements =
      card "c1" "node" 10 20 235 150
    ∷ big 127 55 24 "N = 1"
    ∷ txt 127 105 21 "t* = g ∘ t_ω"
    ∷ flow 245 95 290 95 "am"
    ∷ card "c2" "node" 290 20 235 150
    ∷ big 407 55 24 "N = 2"
    ∷ txt 407 98 19 "g(y₁) + g(y₂)"
    ∷ txt 407 126 19 "= h(y₁ + y₂)"
    ∷ flow 525 95 570 95 "am"
    ∷ card "c3" "node" 570 20 235 150
    ∷ big 687 55 24 "Cauchy"
    ∷ txt 687 105 21 "g is affine"
    ∷ flow 805 95 850 95 "am"
    ∷ card "c4" "node" 850 20 235 150
    ∷ big 967 55 24 "every N"
    ∷ txt 967 98 19 "mean-pool is"
    ∷ txt 967 126 19 "sufficient"
    ∷ [] }

------------------------------------------------------------------------
-- Slide 9: a result

results : Diagram
results = record
  { name = "d-results" ; width = 560 ; height = 380 ; percent = 100
  ; elements =
      line 30 300 540 300 (cls "axis")
    ∷ rect 60  66 120 234 (cls "bar b1")
    ∷ rect 220 230 120 70 (cls "bar b2")
    ∷ rect 380 290 120 10 (cls "bar b3")
    ∷ label 120 46 24 "1.17" (cls "stat plum count")
    ∷ label 280 210 24 "0.35" (cls "stat count")
    ∷ label 440 270 24 "0.05" (cls "stat rust count")
    ∷ big 120 325 19 "N = 1"
    ∷ big 280 325 19 "PAIRS"
    ∷ big 440 325 19 "N = 1–10"
    ∷ dim 120 350 14 "per observation"
    ∷ dim 280 350 14 "pretrained at N ≤ 2"
    ∷ dim 440 350 14 "3–4× the pretraining"
    ∷ dim 285 14 15 "test NLL, Circle Radius, N = 1000 (lower is better)"
    ∷ [] }

------------------------------------------------------------------------
-- Slide 10: cost and scale

tiles : Diagram
tiles = record
  { name = "d-tiles" ; width = 1100 ; height = 270 ; percent = 100
  ; elements =
      rect 10  10 255 240 (rounded 20 (cls "tile"))
    ∷ label 137 85 54 "≈100×" (cls "stat count")
    ∷ txt 137 150 19 "less compute than"
    ∷ txt 137 176 19 "end-to-end training"
    ∷ dim 137 214 16 "at N = 1000"
    ∷ rect 285 10 255 240 (rounded 20 (cls "tile"))
    ∷ label 412 85 54 "3–4×" (cls "stat crimson")
    ∷ txt 412 150 19 "cheaper than a larger"
    ∷ txt 412 176 19 "pretraining, N = 1–10"
    ∷ dim 412 214 16 "and no better on 3 of 4 tasks"
    ∷ rect 560 10 255 240 (rounded 20 (cls "tile"))
    ∷ label 687 85 54 "128" (cls "stat rust count")
    ∷ txt 687 150 19 "scenes per batch at N = 2"
    ∷ txt 687 176 19 "(≈ 2 at N = 100)"
    ∷ dim 687 214 16 "one H100-80GB, novel views"
    ∷ rect 835 10 255 240 (rounded 20 (cls "tile"))
    ∷ label 962 85 54 "0.004" (cls "stat plum count")
    ∷ txt 962 150 19 "novel-view MSE at N = 100"
    ∷ txt 962 176 19 "(0.011 at N = 1)"
    ∷ dim 962 214 16 "error falls as the set grows"
    ∷ [] }

------------------------------------------------------------------------
-- The deck

-- q_φ(θ | T_ω(X))
posterior : M.Math
posterior =
  M.call (M.idx "q" (M.greek M.phi))
    (M.rel M.mid θ (M.call (M.idx (M.var "T") (M.greek M.omega)) (X ∷ [])) ∷ [])

-- E_{θ, X} log q_φ(θ | T_ω(X))
objective : M.Math
objective = M.juxt (M.idx (M.bb "E") (M.tuple (θ ∷ X ∷ []))) (M.fn M.log posterior)

-- O(B N_max)
memory : M.Math
memory = M.call "O" (M.juxt "B" (M.idx "N" (M.text "max")) ∷ [])

pairs : Deck
pairs = do

  -- 1 ------------------------------------------------------------------
  slide (do
    mount "hero-title"
    classed "title-copy tag" (Content.paragraph "Neural posterior estimation · Deep Sets")
    classed "title-copy" (Content.heading 1 "It Just Takes Two")
    classed "title-copy subtitle" (Content.paragraph "Scaling Amortized Inference to Large Sets")
    classed "title-copy authors" (Content.paragraph "Antoine Wehenkel · Michael Kagan · Lukas Heinrich · Chris Pollard")
    classed "title-copy small" (Content.paragraph ("arXiv:2605.07972 · " ∷ link "https://arxiv.org/abs/2605.07972" "abstract" ∷ []))
    script "PAIRS.title(slide, 'hero-title')"
    notes "The paper in one line: train a mean-pool Deep Set on sets of at most two elements, then finetune the inference head on cached aggregates.")

  -- 2 ------------------------------------------------------------------
  slide (do
    heading 2 "Inference from a set of observations"
    columns
      ( Content.diagram problem
      ∷ (do Content.bullets
              ( ("a target " ∷ inlineMath θ ∷ ", say a signal fraction" ∷ [])
              ∷ ("a nuisance " ∷ inlineMath ψ ∷ " shared by every observation" ∷ [])
              ∷ ("marginalising " ∷ inlineMath ψ ∷ " couples the " ∷ emph "xᵢ" ∷ [])
              ∷ [])
            Content.displayMath joint)
      ∷ [])
    classed "callout blue"
      (Content.paragraph ("Goal: one amortized " ∷ inlineMath (M.call "q" (M.rel M.mid θ X ∷ []))
                          ∷ " for any set size " ∷ inlineMath N ∷ []))
    script "PAIRS.flow(slide)"
    notes "The posterior does not factorise over observations because they share the nuisance parameter.")

  -- 3 ------------------------------------------------------------------
  slide (do
    heading 2 "A bump hunt, event by event"
    columns
      ( (do Content.mount "bump"
            Content.paragraph "simulated live in your browser: background gray, signal crimson")
      ∷ (do Content.bullets
              ( ("signal fraction " ∷ inlineMath θ ∷ " in [0, 1]" ∷ [])
              ∷ ("signal location " ∷ inlineMath ψ ∷ " unknown" ∷ [])
              ∷ "background fills the whole range"
              ∷ ("only the " ∷ emph "whole set" ∷ " pins down " ∷ inlineMath θ ∷ [])
              ∷ []))
      ∷ [])
    classed "callout"
      (Content.paragraph "At N = 100 the PAIRS posterior width tracks MCMC on the full set; the naive product of per-event posteriors is underconfident.")
    script "PAIRS.bump(slide, 'bump')")

  -- 4 ------------------------------------------------------------------
  slide (do
    heading 2 "Two ways to scale, both costly"
    classed "card plum"
      (do Content.heading 3 "Combine per-observation posteriors"
          Content.paragraph "✓ scales to any set size"
          Content.paragraph ("✗ misses what the observations share through " ∷ inlineMath ψ ∷ []))
    classed "card crimson"
      (do Content.heading 3 "Encode the whole set at deployment size"
          Content.paragraph "✓ principled: the set is seen jointly"
          Content.paragraph ("✗ per step, memory grows as " ∷ inlineMath memory ∷ " and compute with the mean set size" ∷ []))
    pause
    classed "callout blue"
      (Content.paragraph "Can we train small, and still deploy on sets of thousands?"))

  -- 5 ------------------------------------------------------------------
  slide (do
    heading 2 "Building blocks: NPE with a Deep Set"
    diagram pipeline
    displayMath meanPool
    displayMath objective
    script "PAIRS.flow(slide)"
    notes "t_omega is applied to each element; the mean-pooled embedding and N go to the head, a normalising flow or flow-matching model.")

  -- 6 ------------------------------------------------------------------
  slide (do
    heading 2 "PAIRS: train on pairs, finetune on aggregates"
    classed "small" (Content.paragraph "Pretraining Aggregators for Inference at aRbitrary Set-sizes")
    diagram stages
    classed "callout"
      (Content.paragraph "Training memory and compute no longer depend on the largest set size.")
    script "PAIRS.flow(slide); PAIRS.cycle(slide, ['st1', 'st2', 'st3'])")

  -- 7 ------------------------------------------------------------------
  slide (do
    heading 2 "Why two is enough"
    classed "card wide"
      (do Content.heading 3 "Theorem (informally)"
          Content.paragraph ("If a mean-pooled statistic is sufficient at every " ∷ inlineMath N
            ∷ ", a network trained to be sufficient at " ∷ inlineMath (M.rel M.elem N (M.raw "\\{1, 2\\}"))
            ∷ " is sufficient at every " ∷ inlineMath N ∷ ", and the two statistics differ by an affine map." ∷ []))
    diagram chain
    classed "small"
      (Content.paragraph ("At N = 2 the constraint is the additive equation " ∷ inlineMath cauchy
        ∷ ". Mean-pool sufficiency holds exactly when the marginals are an exponential family; errors in pair training degrade gracefully." ∷ []))
    script "PAIRS.flow(slide); PAIRS.cycle(slide, ['c1', 'c2', 'c3', 'c4'], {accumulate: true, seconds: 1.3})")

  -- 8 ------------------------------------------------------------------
  slide (do
    heading 2 "Does it work? Five test beds"
    classed "callout blue"
      (Content.paragraph "Bivariate Gaussian: trained at N ≤ 2, PAIRS tracks the analytic posterior up to N = 10⁵.")
    classed "card plum"
      (do Content.heading 3 "Circle Radius"
          Content.paragraph "Radius of a circle in 64×64 images with distractors; N up to 1000.")
    classed "card"
      (do Content.heading 3 "Digit Expectation"
          Content.paragraph "Expected digit from rotated MNIST images sharing one angle; N up to 1000.")
    classed "card crimson"
      (do Content.heading 3 "3D Object Properties"
          Content.paragraph "Volume and aspect ratio from partial ModelNet40 views.")
    classed "card rust"
      (do Content.heading 3 "Molecular Lipophilicity"
          Content.paragraph "logP from sets of GEOM 3D conformers.")
    classed "small"
      (Content.paragraph "Baselines: N = 1, N = 1–10, a Gaussian head, and end-to-end at N = 1000 (synthetic tasks). Three seeds."))

  -- 9 ------------------------------------------------------------------
  slide (do
    heading 2 "Results"
    columns
      ( Content.diagram results
      ∷ Content.bullets
          ( ("PAIRS " ∷ strong "matches or beats" ∷ " every baseline on nearly all tasks" ∷ [])
          ∷ "improves monotonically with N, though pretrained only at N ≤ 2"
          ∷ "pretraining at N = 1–10 wins on Circle Radius, at 3–4× the cost"
          ∷ "N = 1 falls behind where nuisance coupling matters"
          ∷ [])
      ∷ [])
    script "PAIRS.grow(slide)")

  -- 10 -----------------------------------------------------------------
  slide (do
    heading 2 "Cost and scale"
    diagram tiles
    classed "callout"
      (Content.paragraph "Novel-view synthesis: three coloured spheres, a flow-matching head, one model for N from 1 to 100.")
    script "PAIRS.grow(slide)")

  -- 11 -----------------------------------------------------------------
  slide (do
    mount "hero-end"
    classed "title-copy"
      (do Content.heading 2 "Take-aways"
          Content.bullets
            ( ("train small, " ∷ emph "deploy large" ∷ [])
            ∷ "pairs recover the pooled representation, up to an affine map"
            ∷ "training cost decouples from the deployment set size"
            ∷ "open: max and attention pooling; the exponential-family idealisation"
            ∷ []))
    classed "title-copy closing" (Content.paragraph "It just takes two.")
    classed "title-copy small"
      (Content.paragraph ("Wehenkel, Kagan, Heinrich, Pollard · " ∷ link "https://arxiv.org/abs/2605.07972" "arXiv:2605.07972" ∷ []))
    script "PAIRS.title(slide, 'hero-end')")
