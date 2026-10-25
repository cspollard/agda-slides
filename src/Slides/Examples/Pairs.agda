{-# OPTIONS --safe --without-K #-}

-- An introduction to "It Just Takes Two: Scaling Amortized Inference to Large
-- Sets" (Wehenkel, Kagan, Heinrich, Pollard; arXiv:2605.07972) in eleven
-- slides.  It uses typed math, SVG diagrams, cards and callouts styled by
-- `assets/pairs/pairs.css`, and the animations of `assets/pairs/pairs.js`
-- (point pairs, pulses along arrows, a live histogram, growing bars and
-- counters).  See `docs/PairsDeck.md`.

module Slides.Examples.Pairs where

open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; _+_; _∸_)
open import Data.String using (String) renaming (_++_ to _++ˢ_)

open import Slides.Core using (Deck; emph; strong; inlineMath; link; codeSpan)
open import Slides.DSL
open import Slides.Diagram
open import Slides.Diagram.Layout
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

-- text in the slide colour; `dim` is a muted caption, `big` a heavier title
txt dim big : ℕ → String → Dia
txt  size t = text size t defaultStyle
dim  size t = text size t (cls "dim")
big  size t = bold size t (cls "big")

-- a rounded box of a CSS class with a diagram centred on it; the name is for
-- `connect`, and doubles as the element id that scripts light up
card : String → String → ℕ → ℕ → ℕ → Dia → Dia
card i c r w h d = named i (framed w h (rounded r (withId i (cls c))) d)

-- a flowing arrow: pulses travel along it (`am` crimson, `cy` blue)
flow : String → Style
flow col = cls ("flow " ++ˢ col)

-- arrows from `src`, spread along its south edge, to the north edge of each
-- target (at `endPct` percent along it)
fan : String → ℕ → List String → Style → Dia → Dia
fan src endPct ts s = go 40 ts
  where
    go : ℕ → List String → Dia → Dia
    go p []       d = d
    go p (t ∷ ts) d = go (p + 7) ts (connectP src (at south p) t (at north endPct) s d)

------------------------------------------------------------------------
-- Slide 2: the problem

problem : Diagram
problem = compile "d-problem" 100 (margin 30 0 30 0 (
    fan "th" 40 ("o1" ∷ "o2" ∷ "o3" ∷ "oN" ∷ []) (flow "cy")
      (fan "psi" 60 ("o1" ∷ "o2" ∷ "o3" ∷ "oN" ∷ []) (flow "am")
        (vcat 30
          ( above 142
              (hcat 85
                ( labelAbove 6 (dim 16 "parameter of interest") (named "th" (atop (disc 36 (cls "node blue")) (big 30 "θ")))
                ∷ labelAbove 6 (dim 16 "shared nuisance") (named "psi" (atop (disc 36 (cls "node crimson")) (big 30 "ψ")))
                ∷ []))
              (hcat 20
                ( card "o1" "node" 14 100 54 (txt 22 "x₁")
                ∷ card "o2" "node" 14 100 54 (txt 22 "x₂")
                ∷ card "o3" "node" 14 100 54 (txt 22 "x₃")
                ∷ card "oN" "node" 14 100 54 (txt 22 "x_N")
                ∷ []))
          ∷ dim 18 "one set X = {x₁, …, x_N} sharing the same ψ"
          ∷ [])))))

------------------------------------------------------------------------
-- Slide 5: the building blocks

pipeline : Diagram
pipeline = compile "d-pipeline" 100 (margin 10 0 10 0 (
    connectEW "p1" "t1" (flow "cy") (connectEW "p2" "t2" (flow "cy")
    (connectEW "pn" "tn" (flow "cy")
    (connectP "t1" (side east) "mean" (at west 38) (flow "cy")
    (connectP "t2" (side east) "mean" (side west) (flow "cy")
    (connectP "tn" (side east) "mean" (at west 62) (flow "cy")
    (connectEW "mean" "T" (flow "am") (connectEW "T" "q" (flow "am")
    (connect "N" south "q" north (flow "am")
      (beside 100
        (labelBelow 15 (dim 15 "set elements")
          (vcat 40 ( card "p1" "node" 14 80 50 (txt 20 "x₁")
                   ∷ card "p2" "node" 14 80 50 (txt 20 "x₂")
                   ∷ card "pn" "node" 14 80 50 (txt 20 "x_N") ∷ [])))
        (beside 168
          (labelBelow 15 (dim 15 "same network")
            (vcat 40 ( card "t1" "node blue" 14 100 50 (txt 20 "t_ω")
                     ∷ card "t2" "node blue" 14 100 50 (txt 20 "t_ω")
                     ∷ card "tn" "node blue" 14 100 50 (txt 20 "t_ω") ∷ [])))
          (beside 68
            (labelBelow 15 (dim 15 "any set size")
              (named "mean" (atop (disc 42 (cls "node crimson")) (big 20 "mean"))))
            (beside 60
              (card "T" "node on" 14 130 66 (txt 22 "T_ω(X)"))
              (labelAbove 56 (named "N" (txt 20 "N"))
                (card "q" "node plum" 14 190 66
                  (vcat 0 (txt 22 "q_φ" ∷ dim 15 "posterior over θ" ∷ []))))))))))))))))))

------------------------------------------------------------------------
-- Slide 6: PAIRS

-- A card of centred text lines: a title, body lines and a small note.
-- The id lets scripts light the card up; it is also the name `connect` uses.
infoCard : (id : String) → ℕ → ℕ → ℕ → ℕ → String → List String → List String → Dia
infoCard i w h tsize bsize title body note =
  named i (framed w h (rounded 18 (withId i (cls "node")))
    (topAligned (h ∸ 50)
      (vcat 6 ( text tsize title (cls "big")
              ∷ lines bsize body defaultStyle
              ∷ lines 17 note (cls "dim")
              ∷ []))))

arrowAm : Style
arrowAm = cls "flow am"

stages : Diagram
stages = compile "d-stages" 100 (margin 10 20 10 30 (
    connectEW "st1" "st2" arrowAm (connectEW "st2" "st3" arrowAm (
      hcat 45
        ( infoCard "st1" 330 200 28 22 "1  Pretrain" ("train (ω, φ) jointly" ∷ "on sets of size 1 and 2" ∷ []) ("cheap: tiny sets" ∷ [])
        ∷ infoCard "st2" 330 200 28 22 "2  Cache" ("freeze t_ω, embed every set" ∷ "store the mean T̄ once" ∷ []) ("one pass, parallel" ∷ [])
        ∷ infoCard "st3" 330 200 28 22 "3  Finetune" ("update the head φ only" ∷ "on cached T̄, any N" ∷ []) ("cost ≈ independent of N" ∷ [])
        ∷ [])))))

------------------------------------------------------------------------
-- Slide 7: why pairs are enough

chain : Diagram
chain = compile "d-chain" 100 (margin 10 20 15 20 (
    connectEW "c1" "c2" arrowAm (connectEW "c2" "c3" arrowAm (connectEW "c3" "c4" arrowAm (
      hcat 45
        ( infoCard "c1" 235 150 24 21 "N = 1" ("t* = g ∘ t_ω" ∷ []) []
        ∷ infoCard "c2" 235 150 24 19 "N = 2" ("g(y₁) + g(y₂)" ∷ "= h(y₁ + y₂)" ∷ []) []
        ∷ infoCard "c3" 235 150 24 21 "Cauchy" ("g is affine" ∷ []) []
        ∷ infoCard "c4" 235 150 24 19 "every N" ("mean-pool is" ∷ "sufficient" ∷ []) []
        ∷ []))))))

------------------------------------------------------------------------
-- Slide 9: a result

results : Diagram
results = compile "d-results" 100 (margin 30 0 30 0 (
  above 14 (dim 15 "test NLL, Circle Radius, N = 1000 (lower is better)")
    (above 12
      (above 0
        (hcatA bottom 0
          ( boxWidth 160 (vcat 2 (text 24 "1.17" (cls "stat plum count") ∷ rectangle 120 234 (cls "bar b1") ∷ []))
          ∷ boxWidth 160 (vcat 2 (text 24 "0.35" (cls "stat count") ∷ rectangle 120 70 (cls "bar b2") ∷ []))
          ∷ boxWidth 160 (vcat 2 (text 24 "0.05" (cls "stat rust count") ∷ rectangle 120 10 (cls "bar b3") ∷ []))
          ∷ []))
        (segment 510 0 (cls "axis")))
      (hcat 0
        ( boxWidth 160 (vcat 4 (big 19 "N = 1" ∷ dim 14 "per observation" ∷ []))
        ∷ boxWidth 160 (vcat 4 (big 19 "PAIRS" ∷ dim 14 "pretrained at N ≤ 2" ∷ []))
        ∷ boxWidth 160 (vcat 4 (big 19 "N = 1–10" ∷ dim 14 "3–4× the pretraining" ∷ []))
        ∷ [])))))

------------------------------------------------------------------------
-- Slide 10: cost and scale

-- a tile: a big number (styled by its class), two lines of text and a note
tile : String → String → List String → String → Dia
tile c n body note =
  framed 255 240 (rounded 20 (cls "tile"))
    (topAligned 170
      (vcat 14 ( bold 54 n (cls c)
               ∷ lines 19 body defaultStyle
               ∷ dim 16 note
               ∷ [])))

tiles : Diagram
tiles = compile "d-tiles" 100 (margin 10 10 10 20 (
  hcat 20
    ( tile "stat count" "≈100×" ("less compute than" ∷ "end-to-end training" ∷ []) "at N = 1000"
    ∷ tile "stat crimson" "3–4×" ("cheaper than a larger" ∷ "pretraining, N = 1–10" ∷ []) "and no better on 3 of 4 tasks"
    ∷ tile "stat rust count" "128" ("scenes per batch at N = 2" ∷ "(≈ 2 at N = 100)" ∷ []) "one H100-80GB, novel views"
    ∷ tile "stat plum count" "0.004" ("novel-view MSE at N = 100" ∷ "(0.011 at N = 1)" ∷ []) "error falls as the set grows"
    ∷ [])))

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
