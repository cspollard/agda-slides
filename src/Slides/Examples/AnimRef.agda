{-# OPTIONS --safe --without-K #-}

-- A deck for checking the page player against the frames Agda computes.  Each
-- animation is followed by its frames as ordinary diagrams (`frameDiagrams`, the very
-- list the animation is shipped from, named `ref-…`); `tests/browser/anim-ref.mjs`
-- rebuilds each frame in the page from the first frame and the edits and compares it
-- with the reference.

module Slides.Examples.AnimRef where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Container.FreeMonad using (pure)

open import Slides.Core using (Body; Deck)
open import Slides.DSL
open import Slides.Diagram using (Diagram)
open import Slides.Diagram.Scalar using (natOps)
open import Slides.Anim.Footprint using (parI)
open import Slides.Anim.Render using (frameDiagrams)
open import Slides.Anim.Timeline using (timeline; frames)
open import Slides.Diagram.Syntax using (Dia; atop; rectangle; disc; text; named)
open import Slides.Diagram.Notation using (_∥_; ↔)
open import Slides.Diagram using (defaultStyle; filled)
open import Slides.Diagram.Ordered using (OExpr; natO; termOps; tO; lit; _⊞_; _⊖_; _⊓_; pct)
import Slides.Diagram.Notation as N
open import Slides.Anim.Syntax using (Anim; Seg; tween; tweenT; units; _⨾_; _∥ᵃ_; par)
import Slides.Anim.Track as T
open import Data.Nat using (ℕ; zero; suc; _+_; _*_) 
open import Data.Unit using (⊤)
open import Data.Product using (_,_)
import Data.Rational as ℚ
open import Data.Rational using (ℚ; _/_)
import Data.Integer as ℤ
open import Data.Integer using (ℤ; +_)
import Data.Sign as Sign
open import Data.JSON.AST using (JSON; objectFromList; stringⱼ; numberⱼ; arrayⱼ; jsonNumber; nullⱼ)
open import Data.JSON.Print using (renderJSON)
open import Slides.Diagram.Draw using (Draw; rect; circle; line; arrow; label; Layout)
open import Slides.Anim.Continuous using (frameAt)
open import Slides.Anim.Syntax using (dur)
open import Slides.Examples.Intro using (mover; counter)
open import Slides.Examples.PairsHero using (hero; heroD)

private
  diagrams : List Diagram → Body
  diagrams []       = pure tt
  diagrams (d ∷ ds) = do diagram d; diagrams ds

  steps : Body
  steps = do
    animate "mover" 60 100 (parI natOps mover counter ∷ [])
    diagrams (frameDiagrams "ref-mover" 60 (timeline atop (frames natO) (parI natOps mover counter)))

  -- the same loop as a discrete template (lowered and held): the page's frame at every tick of
  -- the full period must equal the frame Agda computes, and at every quarter tick the frame of the
  -- tick before (the hold; `dhero3`, three pairs, is compared with the exact rationals there)
  dloop : Body
  dloop = do
    animateLoop "dhero" 100 100 (heroD 26 7)
    diagrams (frameDiagrams "ref-dhero" 100 (timeline atop (frames natO) (heroD 26 7)))

  loop : Body
  loop = do
    animateLoop "hero" 100 100 (hero 7)
    diagrams (frameDiagrams "ref-hero" 100 (timeline atop (frames natO) (hero 7)))

------------------------------------------------------------------------
-- Templates.  A template animation is shipped as a simulator (tracks and formulas) that the
-- page evaluates at real time.  The reference is `frameAt` (`Slides.Anim.Continuous`, exact
-- rational arithmetic) at a list of times `τ`, emitted as JSON in a `script` element (the
-- diagrams of the deck hold whole coordinates, the frames at fractional times do not):
--   (`{"ref": name, "taus": [[n,d],…], "frames": [ [ [tag, [n,d],…], … ], … ]}`)
-- with each drawing command as its tag (`rect`, `circle`, `line`, `text`) and numbers in the
-- order of the player's attribute table, positions in drawing units (halved).

private
  module E = N.NotationWith (termOps {⊤})

  ease : T.Easing
  ease = T.Bezier (+ 40) (+ 0) (+ 20) (+ 100)

  orange = filled "#c96" defaultStyle
  blue  = filled "#69c" defaultStyle

  sliderBox : ∀ {V} → Dia (OExpr V)
  sliderBox = named "slider" (rectangle (lit 40) (lit 30) orange)

  slider : T.Easing → ℕ → Anim ℕ (Seg ℕ)
  slider e n = tweenT n (+ 0 / 1) (+ 120 / 1) e (E.↔ tO ∥ sliderBox)

-- a sliderBox sliding right along an easing; the same over 60 and 600 ticks (the formulas are the
-- same size); linear over whole steps (where the discrete frames agree with the continuous);
-- steps that jump
slideT longT vlongT wholeT : Anim ℕ (Seg ℕ)
slideT  = slider ease 6
longT   = slider ease 60
vlongT  = slider ease 600
wholeT  = slider T.Linear 6

stepT : Anim ℕ (Seg ℕ)
stepT = tweenT 4 (+ 0 / 1) (+ 80 / 1) T.Step (E.↔ tO ∥ sliderBox)
      ⨾ tweenT 4 (+ 80 / 1) (+ 120 / 1) T.StepStart (E.↔ tO ∥ sliderBox)

-- a sliderBox that grows (a percentage), a circle that follows it, and a bar that shrinks (a
-- difference, kept non-negative: ℚ's is real subtraction) against a cap (a maximum); two acts
growT : Anim ℕ (Seg ℕ)
growT =
    tweenT 4 (+ 0 / 1) (+ 80 / 1) T.Linear
      (named "g" (rectangle tO (lit 20 ⊞ pct 50 tO) blue) ∥ E.↔ (lit 10) ∥ disc (pct 25 tO) blue)
  ⨾ tweenT 3 (+ 80 / 1) (+ 100 / 1) T.Linear
      (named "g" (rectangle (tO ⊓ lit 90) (lit 100 ⊖ tO) blue) ∥ E.↔ (lit 10) ∥ text 16 "done" defaultStyle)

-- the two together, of different lengths (the segments' parameters are independent), and
-- with the shorter padded (`par`)
bothT padT : Anim ℕ (Seg ℕ)
bothT = slideT ∥ᵃ growT
padT  = par natOps slideT growT

private
  natⱼ : ℕ → JSON
  natⱼ n = numberⱼ (jsonNumber Sign.+ n [] (+ 0))

  rat : ℚ → JSON
  rat q = arrayⱼ (intⱼ (ℚ.↥ q) ∷ natⱼ (ℚ.↧ₙ q) ∷ [])
    where intⱼ : ℤ → JSON
          intⱼ (+ n)      = natⱼ n
          intⱼ (ℤ.-[1+ m ]) = numberⱼ (jsonNumber Sign.- (suc m) [] (+ 0))

  halfQ : ℚ → ℚ
  halfQ x = (+ 1 / 2) ℚ.* x

  drawJ : Draw ℚ → JSON
  drawJ (rect x y w h _)  = arrayⱼ (stringⱼ "rect" ∷ rat (halfQ x) ∷ rat (halfQ y) ∷ rat w ∷ rat h ∷ [])
  drawJ (circle x y r _)  = arrayⱼ (stringⱼ "circle" ∷ rat (halfQ x) ∷ rat (halfQ y) ∷ rat r ∷ [])
  drawJ (line a b c d _)  = arrayⱼ (stringⱼ "line" ∷ rat (halfQ a) ∷ rat (halfQ b) ∷ rat (halfQ c) ∷ rat (halfQ d) ∷ [])
  drawJ (arrow a b c d _) = arrayⱼ (stringⱼ "line" ∷ rat (halfQ a) ∷ rat (halfQ b) ∷ rat (halfQ c) ∷ rat (halfQ d) ∷ [])
  drawJ (label x y _ _ _) = arrayⱼ (stringⱼ "text" ∷ rat (halfQ x) ∷ rat (halfQ y) ∷ [])

  frameJ : Anim ℕ (Seg ℕ) → ℚ → JSON
  frameJ a τ with frameAt a τ
  ... | nothing = nullⱼ
  ... | just l  = arrayⱼ (map drawJ (Layout.draws l))

  -- every tick, and a quarter, a half and three quarters after it, up to the last frame
  taus : ℕ → List ℚ
  taus zero    = []
  taus (suc n) = go 0 n
    where go : ℕ → ℕ → List ℚ
          go k zero    = (+ k / 1) ∷ []
          go k (suc m) = (+ k / 1) ∷ (+ (4 * k + 1) / 4) ∷ (+ (2 * k + 1) / 2) ∷ (+ (4 * k + 3) / 4) ∷ go (suc k) m

  refJSON : String → Anim ℕ (Seg ℕ) → String
  refJSON n a = renderJSON (objectFromList
    ( ("ref" , stringⱼ n)
    ∷ ("taus" , arrayⱼ (map rat ts))
    ∷ ("frames" , arrayⱼ (map (frameJ a) ts))
    ∷ [] ))
    where ts = taus (dur a)

  tpair : String → Anim ℕ (Seg ℕ) → Body
  tpair n a = do
    animate n 60 100 (a ∷ [])
    script ("(" ++ˢ refJSON n a ++ˢ ")")

private
  -- the same slider over 60 ticks, shipped as edits, for the size comparison
  longF : Anim ℕ (Seg ℕ)
  longF = tween 60 (+ 0 / 1) (+ 120 / 1) ease (λ x → ↔ (units x) ∥ named "slider" (rectangle 40 30 orange))


  steps60 : Body
  steps60 = do
    animate "elong" 60 100 (longF ∷ [])
    diagrams (frameDiagrams "ref-elong" 60 (timeline atop (frames natO) longF))

  -- 6 whole steps: the discrete frames (diagrams) must equal the continuous ones at ticks
  wholeF : Anim ℕ (Seg ℕ)
  wholeF = tween 6 (+ 0 / 1) (+ 120 / 1) T.Linear (λ x → ↔ (units x) ∥ named "slider" (rectangle 40 30 orange))

  whole : Body
  whole = do
    tpair "twhole" wholeT
    diagrams (frameDiagrams "ref-twhole" 60 (timeline atop (frames natO) wholeF))

deck : Deck
deck = do
  slide steps
  slide loop
  slide dloop
  slide (tpair "dhero3" (heroD 3 7))
  slide (tpair "tslide" slideT)
  slide (tpair "tlong" longT)
  slide (tpair "tvlong" vlongT)
  slide (tpair "tstep" stepT)
  slide (tpair "tgrow" growT)
  slide (tpair "tboth" bothT)
  slide (tpair "tpad" padT)
  slide whole
  slide steps60
