{-# OPTIONS --without-K #-}

-- The LHC animation: a circular beam pipe viewed at an angle (an ellipse),
-- two counter-circulating proton bunches (orange/rust circles) that collide
-- at the bottom-center of the pipe, and a particle flash on collision.
--
-- The diagram language has no ellipse, so the pipe is a `polyline` through 128 points of it
-- (a closed ring: the last point is the first), drawn round-capped by the CSS class `pipe`.  The
-- bunches ride the same ellipse: a position is a table of 64 values (one per tick of the loop)
-- read by a binary tree of `lt`, so it is a formula in the tick and the template ships formulas, not
-- frames.  The scalar layers have no sine, so the tables come from `trig`, a 17-entry sine table with
-- linear interpolation (under 0.2 % off).  The bunches meet at the bottom at tick 0 and pass each
-- other at the top at tick 32 (two beams in one pipe); only the meeting at the bottom flashes.
--
-- Written over `OOps S` so it can be evaluated either at `ℕ` (for static frames)
-- or at `OExpr ⊤` (as a discrete template for smooth `tweenD` in reveal.js).

module Slides.Examples.LHC where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; map; foldr; applyUpTo; length; splitAt) renaming (_++_ to _++ˡ_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _/_; _%_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Integer using (+_)
import Data.Rational as ℚ
open import Data.Unit using (⊤)

open import Slides.Diagram using (withClass; defaultStyle; Style)
open import Slides.Diagram.Syntax using (Dia; disc; polyline; spacer; place; overlay)
open import Slides.Diagram.Scalar using (Ops)
open import Slides.Diagram.Ordered using (OOps; OrdOps; FloorOps; natO; termO; tO; OExpr)
open import Slides.Anim.Syntax using (Anim; tweenD)
import Slides.Anim.Track as T

------------------------------------------------------------------------
-- Dimensions and period

W H : ℕ
-- every length is in units of 1/K of the original size: whole numbers then round to a quarter of
-- what they did, and the polyline of the pipe is smooth (the page scales the drawing to its width)
K : ℕ
K = 4

W = 480 * K
H = 230 * K

-- ticks in one lap of a bunch
period : ℕ
period = 64

-- the ellipse: centre and radii
CX CY RX RY : ℕ
CX = 240 * K
CY = 100 * K
RX = 220 * K
RY = 85 * K

cls : String → Style
cls c = withClass c defaultStyle

------------------------------------------------------------------------
-- Trigonometry in whole numbers
--
-- An angle is a number of 1/256 turns.  `trig a` is (cos , sin) of it, each as a magnitude
-- in tenthousandths and a flag that it is negative.

-- sin of 0, 5.625°, … 90°, then 90° again so that interpolation at the end has a neighbour
sinTable : List ℕ
sinTable = 0 ∷ 980 ∷ 1951 ∷ 2903 ∷ 3827 ∷ 4714 ∷ 5556 ∷ 6344 ∷ 7071
         ∷ 7730 ∷ 8315 ∷ 8819 ∷ 9239 ∷ 9569 ∷ 9808 ∷ 9952 ∷ 10000 ∷ 10000 ∷ []

nth : ℕ → List ℕ → ℕ
nth _       []       = 0
nth zero    (x ∷ _)  = x
nth (suc k) (_ ∷ xs) = nth k xs

-- sin of a first-quadrant angle (a ≤ 64), interpolated between table entries
qsin : ℕ → ℕ
qsin a = lo + ((hi ∸ lo) * (a % 4)) / 4
  where lo = nth (a / 4) sinTable
        hi = nth (suc (a / 4)) sinTable

-- (cos , sin) in quadrant q at r units into it
quad : ℕ → ℕ → (ℕ × Bool) × (ℕ × Bool)
quad 0 r = (qsin (64 ∸ r) , false) , (qsin r , false)
quad 1 r = (qsin r , true)         , (qsin (64 ∸ r) , false)
quad 2 r = (qsin (64 ∸ r) , true)  , (qsin r , true)
quad _ r = (qsin r , false)        , (qsin (64 ∸ r) , true)

trig : ℕ → (ℕ × Bool) × (ℕ × Bool)
trig a = quad ((a / 64) % 4) (a % 64)

-- a signed value moved up by 10000, so that it is never negative: 0 … 20000
lifted : ℕ × Bool → ℕ
lifted (m , neg) = if neg then 10000 ∸ m else 10000 + m

-- a point on the ellipse at angle a (screen coordinates: y grows downwards, so 64 is the bottom)
ellipseAt : ℕ → ℕ × ℕ
ellipseAt a =
    (CX ∸ RX) + RX * lifted (proj₁ (trig a)) / 10000
  , (CY ∸ RY) + RY * lifted (proj₂ (trig a)) / 10000

-- the first bunch is at angle 64 (the bottom) at tick 0 and turns by 4 units a tick
cosTable sinTableT : List ℕ
cosTable   = map (λ k → lifted (proj₁ (trig (64 + 4 * k)))) (applyUpTo (λ k → k) period)
sinTableT  = map (λ k → lifted (proj₂ (trig (64 + 4 * k)))) (applyUpTo (λ k → k) period)

-- eight directions for the sparks, 45° apart
sparkDirs : List ((ℕ × Bool) × (ℕ × Bool))
sparkDirs = map (λ j → trig (32 * j)) (applyUpTo (λ j → j) 8)

------------------------------------------------------------------------
-- Generic Frame over any scalar S

module PipeFrame {S : Set} (D : OOps S) where
  private
    O = OOps.ops D
  open Ops O renaming (_+_ to _⊕_; _-_ to _⊖_; fromℕ to lit)
  open OrdOps (OOps.ord D) using (lt)
  open FloorOps (OOps.floor D) using (divBy; modBy; mulLit)

  put : S → S → Dia S → Dia S
  put x y = place (lit W) (lit H) x y

  canvas : List (Dia S) → Dia S
  canvas = foldr (λ d acc → overlay (lit W) (lit H) acc d) (spacer (lit W) (lit H))

  -- the pipe: one closed polyline through 128 points of the ellipse (the 129th is the first)
  pipePoint : ℕ → S × S
  pipePoint k = lit (proj₁ (ellipseAt (2 * k))) , lit (proj₂ (ellipseAt (2 * k)))

  pipeRing : List (Dia S)
  pipeRing = put (lit 0) (lit 0) (polyline (map pipePoint (applyUpTo (λ k → k) 129)) (cls "pipe")) ∷ []

  -- the value of a table at the tick u, as a binary tree of comparisons over the indices
  -- `off … off + length vs` (the fuel is the depth of the tree)
  tree : ℕ → S → ℕ → List ℕ → S
  tree zero    u off vs        = lit 0
  tree (suc f) u off []        = lit 0
  tree (suc f) u off (v ∷ [])  = lit v
  tree (suc f) u off vs        =
    lt u (lit (off + length vs / 2))
       (tree f u off (proj₁ (splitAt (length vs / 2) vs)))
       (tree f u (off + length vs / 2) (proj₂ (splitAt (length vs / 2) vs)))

  -- the first bunch, from the tables: x = 80 + 220 (1 + cos), y = 70 + 85 (1 + sin)
  p1X p1Y : S → S
  p1X t = lit (CX ∸ RX) ⊕ divBy 9999 (mulLit RX (tree 8 (modBy 63 t) 0 cosTable))
  p1Y t = lit (CY ∸ RY) ⊕ divBy 9999 (mulLit RY (tree 8 (modBy 63 t) 0 sinTableT))

  -- the second bunch turns the other way: the mirror image in the vertical axis
  p2X : S → S
  p2X t = lit (2 * CX) ⊖ p1X t

  -- the flash after a collision at the bottom, tick 0: a burst that grows for 8 ticks and shrinks
  -- for 8, and sparks that fly out for 16
  burstR : S → S
  burstR u = lt u (lit 8) (mulLit (3 * K) u) (lt u (lit 16) (mulLit (3 * K) (lit 16 ⊖ u)) (lit 0))

  sparkD : S → S
  sparkD u = lt u (lit 16) (lit (6 * K) ⊕ mulLit (3 * K) u) (lit 0)

  sparkR : S → S
  sparkR u = lt u (lit 16) (lit (3 * K)) (lit 0)

  -- a spark flies from the collision point along (cos , sin), squashed to 60 % vertically
  spark : S → (ℕ × Bool) × (ℕ × Bool) → Dia S
  spark u ((cm , cn) , (sm , sn)) =
    let dx = divBy 99 (mulLit (cm / 100) (sparkD u))
        dy = divBy 99 (mulLit (sm * 60 / 10000) (sparkD u))
        x  = if cn then lit CX ⊖ dx else lit CX ⊕ dx
        y  = if sn then lit (CY + RY) ⊖ dy else lit (CY + RY) ⊕ dy
    in put (x ⊖ sparkR u) (y ⊖ sparkR u) (disc (sparkR u) (cls "spark"))

  -- a bunch at (x , y): a soft halo and a core
  bunch : S → S → List (Dia S)
  bunch x y =
      put (x ⊖ lit (11 * K)) (y ⊖ lit (11 * K)) (disc (lit (11 * K)) (cls "halo"))
    ∷ put (x ⊖ lit (7 * K)) (y ⊖ lit (7 * K)) (disc (lit (7 * K)) (cls "bunch"))
    ∷ []

  lhcDia : S → Dia S
  lhcDia t =
    let u = modBy 63 t
        r = burstR u
    in canvas
         ( pipeRing
         ++ˡ bunch (p1X t) (p1Y t)
         ++ˡ bunch (p2X t) (p1Y t)
         ++ˡ (put (lit CX ⊖ r) (lit (CY + RY) ⊖ r) (disc r (cls "burst"))
              ∷ map (spark u) sparkDirs))

------------------------------------------------------------------------
-- Exported Diagrams and Animations

lhcFrameAt : ℕ → Dia ℕ
lhcFrameAt = PipeFrame.lhcDia natO

lhcTemplate : Dia (OExpr ⊤)
lhcTemplate = PipeFrame.lhcDia termO tO

-- Smooth parametric loop: one frame per tick, `period` ticks to a lap
lhcAnim : Anim
lhcAnim = tweenD period (+ 0 ℚ./ 1) (+ period ℚ./ 1) T.Linear lhcTemplate
