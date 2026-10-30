{-# OPTIONS --safe --without-K #-}

-- "It Just Takes Two: Scaling Amortized Inference to Large Sets" (Wehenkel, Kagan, Heinrich,
-- Pollard; arXiv:2605.07972), eleven slides.  Shows typed math, SVG diagrams styled by
-- `assets/pairs/pairs.css`, and all animation kinds with no hand-written JS: loops (hero pairs,
-- marching arrows), steps over a loop (`animateBoth`), Bézier flip books (`grow`).
-- Build with `make pairs`.

module Slides.Examples.Pairs where

open import Data.List using (List; _∷_; []; map; zipWith; upTo)
open import Data.Bool using (Bool; false; if_then_else_)
open import Data.Nat using (ℕ; _+_; _∸_; _≡ᵇ_; _≤ᵇ_; _<ᵇ_; _/_; _%_)
open import Data.Nat.Show using (show)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
import Data.Rational as ℚ

open import Slides.Scalar.Time using (Time)
open import Slides.Deck.Anim using (Anim; frame′; frames; flipTween; liftDia; ι; ratTime; Bezier; _⨾_)
open import Slides.Deck.Talk using (Talk)
open import Slides.Deck.DSL hiding (text)
open import Slides.Diagram.Convenience
open import Slides.Diagram.Names using (dangling)
open import Slides.Examples.PairsHero using (heroLoop)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Slides.Math as M

open Content using () renaming (paragraph to p■; heading to h■)

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

-- a flowing arrow: its dashes march along it (`am` crimson, `cy` blue)
-- at phase `ph` of the march (see `marching`)
flow : ℕ → String → Style
flow ph col = cls ("flow " ++ˢ col ++ˢ " ph" ++ˢ show ph)

-- one period of a march: the phases `0 … 7`, one frame each, run once through the loop
marching : (ℕ → Dia ℕ) → Anim
marching f = frames (map f (upTo 8))

-- arrows from `src`, spread along its south edge, to the north edge of each
-- target (at `endPct` percent along it)
fan : String → ℕ → List String → List Edge
fan src endPct = go 40
  where
    go : ℕ → List String → List Edge
    go p []       = []
    go p (t ∷ ts) = (src ⊢ at south p ⇒ t ⊢ at north endPct) ∷ go (p + 7) ts

------------------------------------------------------------------------
-- The problem

problemDia : ℕ → Dia ℕ
problemDia ph =
  margin 30 0 30 0 (body ▹[ flow ph "cy" ] fan "th" 40 targets ▹[ flow ph "am" ] fan "psi" 60 targets)
  where
    targets = "o1" ∷ "o2" ∷ "o3" ∷ "oN" ∷ []
    params =
      ⟨ (dim 16 "parameter of interest" ⌃[ 6 ] ("th" ⦂ disc 36 (cls "node blue") ⊙ big 30 "θ"))
      ∷ (dim 16 "shared nuisance"       ⌃[ 6 ] ("psi" ⦂ disc 36 (cls "node crimson") ⊙ big 30 "ψ"))
      ∷ [] ⟩ₕ 85
    observed =
      ⟨ card "o1" "node" 14 100 54 (txt 22 "x₁")
      ∷ card "o2" "node" 14 100 54 (txt 22 "x₂")
      ∷ card "o3" "node" 14 100 54 (txt 22 "x₃")
      ∷ card "oN" "node" 14 100 54 (txt 22 "x_N")
      ∷ [] ⟩ₕ 20
    body = (params ═ ↕ 142 ═ observed) ═ ↕ 30 ═ dim 18 "one set X = {x₁, …, x_N} sharing the same ψ"

problem : Flow
problem = Content.animateLoop "d-problem" 100 90 (marching problemDia)

------------------------------------------------------------------------
-- The building blocks

pipelineDia : ℕ → Dia ℕ
pipelineDia ph =
  margin 10 0 10 0
    (body ▹[ flow ph "cy" ] ( "p1" ⟶ "t1" ∷ "p2" ⟶ "t2" ∷ "pn" ⟶ "tn"
                         ∷ "t1" ⊢ side east ⇒ "mean" ⊢ at west 38
                         ∷ "t2" ⊢ side east ⇒ "mean" ⊢ side west
                         ∷ "tn" ⊢ side east ⇒ "mean" ⊢ at west 62 ∷ [] )
          ▹[ flow ph "am" ] ( "mean" ⟶ "T" ∷ "T" ⟶ "q" ∷ "N" ⟱ "q" ∷ [] ))
  where
    elements =
      ⟨ card "p1" "node" 14 80 50 (txt 20 "x₁")
      ∷ card "p2" "node" 14 80 50 (txt 20 "x₂")
      ∷ card "pn" "node" 14 80 50 (txt 20 "x_N") ∷ [] ⟩ᵥ 40
    networks =
      ⟨ card "t1" "node blue" 14 100 50 (txt 20 "t_ω")
      ∷ card "t2" "node blue" 14 100 50 (txt 20 "t_ω")
      ∷ card "tn" "node blue" 14 100 50 (txt 20 "t_ω") ∷ [] ⟩ᵥ 40
    pool = "mean" ⦂ (disc 42 (cls "node crimson") ⊙ big 20 "mean")
    posterior = card "q" "node plum" 14 190 66 (txt 22 "q_φ" ═ dim 15 "posterior over θ")
    body =
        elements ⌄[ 15 ] dim 15 "set elements"
      ∥ ↔ 100 ∥ networks ⌄[ 15 ] dim 15 "same network"
      ∥ ↔ 168 ∥ pool ⌄[ 15 ] dim 15 "any set size"
      ∥ ↔ 68 ∥ card "T" "node on" 14 130 66 (txt 22 "T_ω(X)")
      ∥ ↔ 60 ∥ ("N" ⦂ txt 20 "N") ⌃[ 56 ] posterior

pipeline : Flow
pipeline = Content.animateLoop "d-pipeline" 100 90 (marching pipelineDia)

------------------------------------------------------------------------
-- PAIRS

-- A card of centred text lines: a title, body lines and a small note.
-- `on` lights the card up (the CSS class `on`); the name is for `connect`.
infoCard : Bool → (id : String) → ℕ → ℕ → ℕ → ℕ → String → List String → List String → Dia ℕ
infoCard on i w h tsize bsize title body note =
  named i (framed w h (rounded 18 (cls (if on then "node on" else "node")))
    (topAligned (h ∸ 50)
      (vcat 6 ( text tsize title (cls "big")
              ∷ lines bsize body defaultStyle
              ∷ lines 17 note (cls "dim")
              ∷ []))))


-- the diagram with the stages `lit` shown highlighted
stagesDia : (ℕ → Bool) → ℕ → Dia ℕ
stagesDia lit ph =
  margin 10 20 10 30
    (⟨ infoCard (lit 1) "st1" 330 200 28 22 "1  Pretrain" ("train (ω, φ) jointly" ∷ "on sets of size 1 and 2" ∷ []) ("cheap: tiny sets" ∷ [])
     ∷ infoCard (lit 2) "st2" 330 200 28 22 "2  Cache" ("freeze t_ω, embed every set" ∷ "store the mean T̄ once" ∷ []) ("one pass, parallel" ∷ [])
     ∷ infoCard (lit 3) "st3" 330 200 28 22 "3  Finetune" ("update the head φ only" ∷ "on cached T̄, any N" ∷ []) ("cost ≈ independent of N" ∷ [])
     ∷ [] ⟩ₕ 45
     ▹[ flow ph "am" ] ("st1" ⟶ "st2" ∷ "st2" ⟶ "st3" ∷ []))

-- one reveal step lights up the next stage (the first also shows the unlit diagram)
still′ : Dia ℕ → Anim
still′ d = frame′ 1 (liftDia d)

stageActs : ℕ → List Anim
stageActs ph = (still′ (stagesDia (λ _ → false) ph) ⨾ still′ (stagesDia (_≡ᵇ 1) ph))
             ∷ still′ (stagesDia (_≡ᵇ 2) ph)
             ∷ still′ (stagesDia (_≡ᵇ 3) ph)
             ∷ []

------------------------------------------------------------------------
-- Why pairs are enough

-- the diagram with the first `k` links lit
chainDia : ℕ → ℕ → Dia ℕ
chainDia k ph =
  margin 10 20 15 20
    (⟨ infoCard (1 ≤ᵇ k) "c1" 235 150 24 21 "N = 1" ("t* = g ∘ t_ω" ∷ []) []
     ∷ infoCard (2 ≤ᵇ k) "c2" 235 150 24 19 "N = 2" ("g(y₁) + g(y₂)" ∷ "= h(y₁ + y₂)" ∷ []) []
     ∷ infoCard (3 ≤ᵇ k) "c3" 235 150 24 21 "Cauchy" ("g is affine" ∷ []) []
     ∷ infoCard (4 ≤ᵇ k) "c4" 235 150 24 19 "every N" ("mean-pool is" ∷ "sufficient" ∷ []) []
     ∷ [] ⟩ₕ 45
     ▹[ flow ph "am" ] ("c1" ⟶ "c2" ∷ "c2" ⟶ "c3" ∷ "c3" ⟶ "c4" ∷ []))

-- one reveal step lights one more link; earlier ones stay lit
chainActs : ℕ → List Anim
chainActs ph = (still′ (chainDia 0 ph) ⨾ still′ (chainDia 1 ph))
             ∷ still′ (chainDia 2 ph)
             ∷ still′ (chainDia 3 ph)
             ∷ still′ (chainDia 4 ph)
             ∷ []

------------------------------------------------------------------------
-- Growing: a parameter `q` runs from 0 to 1 along an ease-out curve (a cubic Bézier), and the
-- diagram is a function of it: a flip book of `ticks` frames, then the end state: one act, one
-- reveal step

grow : ℕ → (ℚ.ℚ → Dia ℕ) → Anim
grow ticks f = flipTween ticks (Bezier 20 90 20 100) f ⨾ still′ (f (ι 1))

-- `q` of a quantity, in whole units
part : ℚ.ℚ → ℕ → ℕ
part q v = Time.floor ratTime (q ℚ.* ι v)

-- a number of hundredths / thousandths as a decimal
fixed2 fixed3 : ℕ → String
fixed2 n = show (n / 100) ++ˢ "." ++ˢ pad 10 (n % 100)
  where pad : ℕ → ℕ → String
        pad lim k = if k <ᵇ lim then "0" ++ˢ show k else show k
fixed3 n = show (n / 1000) ++ˢ "." ++ˢ pad (n % 1000)
  where pad : ℕ → String
        pad k = if k <ᵇ 10 then "00" ++ˢ show k else if k <ᵇ 100 then "0" ++ˢ show k else show k

------------------------------------------------------------------------
-- A bump hunt

-- Bin heights (pixels) of 2500 simulated events: a standard-normal background
-- and a narrow signal bump at ψ = 1.8 with θ = 0.12 (one realisation, 36 bins
-- over [-4, 5]).  The animation fills the histogram: at parameter `q` each bar
-- stands `q` of the way up and the caption counts `q` of the events.
backgroundBins signalBins : List ℕ
backgroundBins = 1 ∷ 0 ∷ 1 ∷ 3 ∷ 4 ∷ 6 ∷ 15 ∷ 18 ∷ 34 ∷ 49 ∷ 87 ∷ 101 ∷ 137 ∷ 158 ∷ 205 ∷ 230 ∷ 178 ∷ 203 ∷ 169 ∷ 133 ∷ 119 ∷ 85 ∷ 61 ∷ 42 ∷ 22 ∷ 16 ∷ 7 ∷ 3 ∷ 2 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
signalBins     = 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 93 ∷ 188 ∷ 6 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

-- a bar of the histogram: signal stacked on background, `q` of the way up
histBar : ℚ.ℚ → ℕ → ℕ → Dia ℕ
histBar q b s = ↔ 2 ∥ (rectangle 12 (part q s) (cls "hist-sig") ═ rectangle 12 (part q b) (cls "hist-bkg"))

histogram : ℚ.ℚ → Dia ℕ
histogram q =
  margin 10 0 10 0
    (dim 18 ("N = " ++ˢ show (part q 2500) ++ˢ " events") ═ ↕ 10
     ═ ((↔ 55 ∥ hcatA bottom 0 (zipWith (histBar q) backgroundBins signalBins)) ═ segment 500 0 (cls "axis"))
     ═ ↕ 6 ═ ticks)
  where
    ticks = ↔ 0 ∥ hcat 0 (map (λ t → boxWidth 111 (dim 16 t)) ("-4" ∷ "-2" ∷ "0" ∷ "2" ∷ "4" ∷ []))

bump : Flow
bump = Content.animate "bump" 100 130 (grow 12 histogram ∷ [])

------------------------------------------------------------------------
-- A result

resultsDia : ℚ.ℚ → Dia ℕ
resultsDia q =
  margin 30 0 30 0
    (dim 15 "test NLL, Circle Radius, N = 1000 (lower is better)" ═ ↕ 14
     ═ (bars ═ segment 510 0 (cls "axis")) ═ ↕ 12 ═ captions)
  where
    column : Dia ℕ → Dia ℕ
    column = boxWidth 160
    bars =
      hcatA bottom 0
        ( column (text 24 (fixed2 (part q 117)) (cls "stat plum") ═ ↕ 2 ═ rectangle 120 (part q 234) (cls "b1"))
        ∷ column (text 24 (fixed2 (part q 35)) (cls "stat") ═ ↕ 2 ═ rectangle 120 (part q 70) (cls "b2"))
        ∷ column (text 24 (fixed2 (part q 5)) (cls "stat rust") ═ ↕ 2 ═ rectangle 120 (part q 10) (cls "b3"))
        ∷ [])
    captions =
      ⟨ column (big 19 "N = 1" ═ ↕ 4 ═ dim 14 "per observation")
      ∷ column (big 19 "PAIRS" ═ ↕ 4 ═ dim 14 "pretrained at N ≤ 2")
      ∷ column (big 19 "N = 1–10" ═ ↕ 4 ═ dim 14 "3–4× the pretraining")
      ∷ [] ⟩ₕ 0

results : Flow
results = Content.animate "d-results" 100 130 (grow 10 resultsDia ∷ [])

------------------------------------------------------------------------
-- Cost and scale

-- a tile: a big number (styled by its class), two lines of text and a note
tile : String → String → List String → String → Dia ℕ
tile c n body note =
  framed 255 240 (rounded 20 (cls "tile"))
    (topAligned 170
      (vcat 14 ( bold 54 n (cls c)
               ∷ lines 19 body defaultStyle
               ∷ dim 16 note
               ∷ [])))

tilesDia : ℚ.ℚ → Dia ℕ
tilesDia q =
  margin 10 10 10 20 (
  hcat 20
    ( tile "stat" ("≈" ++ˢ show (part q 100) ++ˢ "×") ("less compute than" ∷ "end-to-end training" ∷ []) "at N = 1000"
    ∷ tile "stat crimson" "3–4×" ("cheaper than a larger" ∷ "pretraining, N = 1–10" ∷ []) "and no better on 3 of 4 tasks"
    ∷ tile "stat rust" (show (part q 128)) ("scenes per batch at N = 2" ∷ "(≈ 2 at N = 100)" ∷ []) "one H100-80GB, novel views"
    ∷ tile "stat plum" (fixed3 (part q 4)) ("novel-view MSE at N = 100" ∷ "(0.011 at N = 1)" ∷ []) "error falls as the set grows"
    ∷ []))

tiles : Flow
tiles = Content.animate "d-tiles" 100 130 (grow 10 tilesDia ∷ [])

-- Every `connect` refers to a name that is declared; a misspelling stops the
-- deck from typechecking (see `Slides.Diagram.Names`).
_ : dangling (problemDia 0) ≡ []
_ = refl
_ : dangling (pipelineDia 0) ≡ []
_ = refl
_ : dangling (stagesDia (λ _ → false) 0) ≡ []
_ = refl
_ : dangling (chainDia 0 0) ≡ []
_ = refl

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

pairs : Talk
pairs = do

  slide (do
    classed "hero-bg hero-title" (Content.animateLoop "hero-title" 100 100 (heroLoop 26 7))
    classed "title-copy tag" (p■ "Neural posterior estimation · Deep Sets")
    classed "title-copy" (h■ 1 "It Just Takes Two")
    classed "title-copy subtitle" (p■ "Scaling Amortized Inference to Large Sets")
    classed "title-copy authors" (p■ "Antoine Wehenkel · Michael Kagan · Lukas Heinrich · Chris Pollard")
    classed "title-copy small" (p■ ("arXiv:2605.07972 · " ∷ link "https://arxiv.org/abs/2605.07972" "abstract" ∷ []))
    notes "The paper in one line: train a mean-pool Deep Set on sets of at most two elements, then finetune the inference head on cached aggregates.")

  slide (do
    heading 2 "Inference from a set of observations"
    columns
      ( problem
      ∷ (do Content.bullets
              ( ("a target " ∷ inlineMath θ ∷ ", say a signal fraction" ∷ [])
              ∷ ("a nuisance " ∷ inlineMath ψ ∷ " shared by every observation" ∷ [])
              ∷ ("marginalising " ∷ inlineMath ψ ∷ " couples the " ∷ emph "xᵢ" ∷ [])
              ∷ [])
            Content.displayMath joint)
      ∷ [])
    classed "callout blue"
      (p■ ("Goal: one amortized " ∷ inlineMath (M.call "q" (M.rel M.mid θ X ∷ []))
                          ∷ " for any set size " ∷ inlineMath N ∷ []))
    notes "The posterior does not factorise over observations because they share the nuisance parameter.")

  slide (do
    heading 2 "A bump hunt, event by event"
    columns
      ( (do bump
            p■ "simulated events: background gray, signal crimson")
      ∷ (do Content.bullets
              ( ("signal fraction " ∷ inlineMath θ ∷ " in [0, 1]" ∷ [])
              ∷ ("signal location " ∷ inlineMath ψ ∷ " unknown" ∷ [])
              ∷ "background fills the whole range"
              ∷ ("only the " ∷ emph "whole set" ∷ " pins down " ∷ inlineMath θ ∷ [])
              ∷ []))
      ∷ [])
    classed "callout"
      (p■ "At N = 100 the PAIRS posterior width tracks MCMC on the full set; the naive product of per-event posteriors is underconfident."))

  slide (do
    heading 2 "Two ways to scale, both costly"
    classed "card plum"
      (do h■ 3 "Combine per-observation posteriors"
          p■ "✓ scales to any set size"
          p■ ("✗ misses what the observations share through " ∷ inlineMath ψ ∷ []))
    classed "card crimson"
      (do h■ 3 "Encode the whole set at deployment size"
          p■ "✓ principled: the set is seen jointly"
          p■ ("✗ per step, memory grows as " ∷ inlineMath memory ∷ " and compute with the mean set size" ∷ []))
    pause
    classed "callout blue"
      (p■ "Can we train small, and still deploy on sets of thousands?"))

  slide (do
    heading 2 "Building blocks: NPE with a Deep Set"
    liftContent pipeline
    displayMath meanPool
    displayMath objective
    notes "t_omega is applied to each element; the mean-pooled embedding and N go to the head, a normalising flow or flow-matching model.")

  slide (do
    heading 2 "PAIRS: train on pairs, finetune on aggregates"
    classed "small" (p■ "Pretraining Aggregators for Inference at aRbitrary Set-sizes")
    animateBoth "d-stages" 100 90 8 stageActs
    classed "callout"
      (p■ "Training memory and compute no longer depend on the largest set size."))

  slide (do
    heading 2 "Why two is enough"
    classed "card wide"
      (do h■ 3 "Theorem (informally)"
          p■ ("If a mean-pooled statistic is sufficient at every " ∷ inlineMath N
            ∷ ", a network trained to be sufficient at " ∷ inlineMath (M.rel M.elem N (M.raw "\\{1, 2\\}"))
            ∷ " is sufficient at every " ∷ inlineMath N ∷ ", and the two statistics differ by an affine map." ∷ []))
    animateBoth "d-chain" 100 90 8 chainActs
    classed "small"
      (p■ ("At N = 2 the constraint is the additive equation " ∷ inlineMath cauchy
        ∷ ". Mean-pool sufficiency holds exactly when the marginals are an exponential family; errors in pair training degrade gracefully." ∷ [])))

  slide (do
    heading 2 "Does it work? Five test beds"
    classed "callout blue"
      (p■ "Bivariate Gaussian: trained at N ≤ 2, PAIRS tracks the analytic posterior up to N = 10⁵.")
    classed "card plum"
      (do h■ 3 "Circle Radius"
          p■ "Radius of a circle in 64×64 images with distractors; N up to 1000.")
    classed "card"
      (do h■ 3 "Digit Expectation"
          p■ "Expected digit from rotated MNIST images sharing one angle; N up to 1000.")
    classed "card crimson"
      (do h■ 3 "3D Object Properties"
          p■ "Volume and aspect ratio from partial ModelNet40 views.")
    classed "card rust"
      (do h■ 3 "Molecular Lipophilicity"
          p■ "logP from sets of GEOM 3D conformers.")
    classed "small"
      (p■ "Baselines: N = 1, N = 1–10, a Gaussian head, and end-to-end at N = 1000 (synthetic tasks). Three seeds."))

  slide (do
    heading 2 "Results"
    columns
      ( results
      ∷ Content.bullets
          ( ("PAIRS " ∷ strong "matches or beats" ∷ " every baseline on nearly all tasks" ∷ [])
          ∷ "improves monotonically with N, though pretrained only at N ≤ 2"
          ∷ "pretraining at N = 1–10 wins on Circle Radius, at 3–4× the cost"
          ∷ "N = 1 falls behind where nuisance coupling matters"
          ∷ [])
      ∷ [])
    )

  slide (do
    heading 2 "Cost and scale"
    liftContent tiles
    classed "callout"
      (p■ "Novel-view synthesis: three coloured spheres, a flow-matching head, one model for N from 1 to 100.")
    )

  slide (do
    classed "hero-bg hero-end" (Content.animateLoop "hero-end" 100 100 (heroLoop 26 13))
    classed "title-copy"
      (do h■ 2 "Take-aways"
          Content.bullets
            ( ("train small, " ∷ emph "deploy large" ∷ [])
            ∷ "pairs recover the pooled representation, up to an affine map"
            ∷ "training cost decouples from the deployment set size"
            ∷ "open: max and attention pooling; the exponential-family idealisation"
            ∷ []))
    classed "title-copy closing" (p■ "It just takes two.")
    classed "title-copy small"
      (p■ ("Wehenkel, Kagan, Heinrich, Pollard · " ∷ link "https://arxiv.org/abs/2605.07972" "arXiv:2605.07972" ∷ []))
    )
