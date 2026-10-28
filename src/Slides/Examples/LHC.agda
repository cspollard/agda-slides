{-# OPTIONS --without-K #-}

-- The LHC animation: a circular beam pipe viewed at an angle (an ellipse),
-- two counter-circulating proton bunches (orange/rust circles) that collide
-- at the bottom-center of the pipe, and a particle flash on collision.
--
-- Written over `OOps S` so it can be evaluated either at `ℕ` (for static frames)
-- or at `OExpr ⊤` (as a discrete template for smooth `tweenD` in reveal.js).

module Slides.Examples.LHC where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; foldr; applyUpTo) renaming (_++_ to _++ˡ_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _/_; _%_; _⊓_) renaming (_⊔_ to _⊔ᴺ_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.Integer using (+_)
import Data.Rational as ℚ
open import Data.Unit using (⊤)

open import Slides.Diagram using (withClass; defaultStyle; Style)
open import Slides.Diagram.Syntax using (Dia; disc; segment; spacer; place; overlay)
open import Slides.Diagram.Scalar using (Ops)
open import Slides.Diagram.Ordered using (OOps; OrdOps; FloorOps; natO; termO; tO; OExpr)
open import Slides.Anim.Syntax using (Anim; tweenD)
import Slides.Anim.Track as T

------------------------------------------------------------------------
-- Dimensions and Period

W H : ℕ
W = 600
H = 340

period : ℕ
period = 32

CX CY RX RY : ℕ
CX = 300
CY = 155
RX = 220
RY = 85

cls : String → Style
cls c = withClass c defaultStyle

------------------------------------------------------------------------
-- 16-point Ellipse Geometry (scaled to 1000)

cos1000 sin1000 : ℕ → ℕ × Bool
cos1000 0  = 1000 , false
cos1000 1  = 924  , false
cos1000 2  = 707  , false
cos1000 3  = 383  , false
cos1000 4  = 0    , false
cos1000 5  = 383  , true
cos1000 6  = 707  , true
cos1000 7  = 924  , true
cos1000 8  = 1000 , true
cos1000 9  = 924  , true
cos1000 10 = 707  , true
cos1000 11 = 383  , true
cos1000 12 = 0    , false
cos1000 13 = 383  , false
cos1000 14 = 707  , false
cos1000 15 = 924  , false
cos1000 _  = 0    , false

sin1000 0  = 0    , false
sin1000 1  = 383  , false
sin1000 2  = 707  , false
sin1000 3  = 924  , false
sin1000 4  = 1000 , false
sin1000 5  = 924  , false
sin1000 6  = 707  , false
sin1000 7  = 383  , false
sin1000 8  = 0    , false
sin1000 9  = 383  , true
sin1000 10 = 707  , true
sin1000 11 = 924  , true
sin1000 12 = 1000 , true
sin1000 13 = 924  , true
sin1000 14 = 707  , true
sin1000 15 = 383  , true
sin1000 _  = 0    , false

ellipsePt : ℕ → ℕ × ℕ
ellipsePt k =
  let (cxm , cneg) = cos1000 (k % 16)
      (sym , sneg) = sin1000 (k % 16)
      dx = (RX * cxm) / 1000
      dy = (RY * sym) / 1000
      px = if cneg then CX ∸ dx else CX + dx
      py = if sneg then CY ∸ dy else CY + dy
  in px , py

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

  -- static ring boundary segment
  pipeSeg : ℕ × ℕ → ℕ × ℕ → Dia S
  pipeSeg (x1 , y1) (x2 , y2) =
    let minX = x1 ⊓ x2
        minY = y1 ⊓ y2
        w = (x1 ⊔ᴺ x2) ∸ minX
        h = (y1 ⊔ᴺ y2) ∸ minY
    in put (lit minX) (lit minY) (segment (lit w) (lit h) (cls "eb"))

  pipeRing : List (Dia S)
  pipeRing =
    applyUpTo (λ i → pipeSeg (ellipsePt i) (ellipsePt (suc i % 16))) 16

  -- Proton positions along the 4 quarter arcs of the ellipse:
  -- bottom-center is at (CX, CY + RY) = (300, 240)
  -- left vertex is at (CX - RX, CY) = (80, 155)
  -- top-center is at (CX, CY - RY) = (300, 70)
  -- right vertex is at (CX + RX, CY) = (520, 155)
  --
  -- With period = 32, each quarter is 8 ticks long.
  -- Proton 1 (clockwise from bottom):
  --   0..8:   x: 300 -> 80  (step -27.5), y: 240 -> 155 (step -10.6)
  --   8..16:  x: 80 -> 300  (step +27.5), y: 155 -> 70  (step -10.6)
  --   16..24: x: 300 -> 520 (step +27.5), y: 70 -> 155  (step +10.6)
  --   24..32: x: 520 -> 300 (step -27.5), y: 155 -> 240 (step +10.6)

  p1X : S → S
  p1X t =
    let u = modBy 31 t -- 0..31
    in lt u (lit 8)
          (lit 300 ⊖ divBy 7 (mulLit 220 u))
          (lt u (lit 16)
              (lit 80 ⊕ divBy 7 (mulLit 220 (u ⊖ lit 8)))
              (lt u (lit 24)
                  (lit 300 ⊕ divBy 7 (mulLit 220 (u ⊖ lit 16)))
                  (lit 520 ⊖ divBy 7 (mulLit 220 (u ⊖ lit 24)))))

  p1Y : S → S
  p1Y t =
    let u = modBy 31 t
    in lt u (lit 8)
          (lit 240 ⊖ divBy 7 (mulLit 85 u))
          (lt u (lit 16)
              (lit 155 ⊖ divBy 7 (mulLit 85 (u ⊖ lit 8)))
              (lt u (lit 24)
                  (lit 70 ⊕ divBy 7 (mulLit 85 (u ⊖ lit 16)))
                  (lit 155 ⊕ divBy 7 (mulLit 85 (u ⊖ lit 24)))))

  -- Proton 2 (counter-clockwise from bottom):
  --   0..8:   x: 300 -> 520 (step +27.5), y: 240 -> 155 (step -10.6)
  --   8..16:  x: 520 -> 300 (step -27.5), y: 155 -> 70  (step -10.6)
  --   16..24: x: 300 -> 80  (step -27.5), y: 70 -> 155  (step +10.6)
  --   24..32: x: 80 -> 300  (step +27.5), y: 155 -> 240 (step +10.6)

  p2X : S → S
  p2X t =
    let u = modBy 31 t
    in lt u (lit 8)
          (lit 300 ⊕ divBy 7 (mulLit 220 u))
          (lt u (lit 16)
              (lit 520 ⊖ divBy 7 (mulLit 220 (u ⊖ lit 8)))
              (lt u (lit 24)
                  (lit 300 ⊖ divBy 7 (mulLit 220 (u ⊖ lit 16)))
                  (lit 80 ⊕ divBy 7 (mulLit 220 (u ⊖ lit 24)))))

  p2Y : S → S
  p2Y = p1Y

  -- Flash bursts at collision: radius and particle sparks expand during u < 4
  flashRadius : S → S
  flashRadius t =
    let u = modBy 31 t
    in lt u (lit 4) (lit 4 ⊕ mulLit 4 u) (lit 0)

  flashSparks : S → List (Dia S)
  flashSparks t =
    let u = modBy 31 t
        r = flashRadius t
        cx = lit 300
        cy = lit 240
    in put (cx ⊖ r) (cy ⊖ r) (disc r (cls "stat crimson"))
     ∷ put (cx ⊖ divBy 1 r) (cy ⊖ divBy 1 r) (disc (divBy 1 r) (cls "stat rust"))
     ∷ []

  lhcDia : S → Dia S
  lhcDia t =
    let x1 = p1X t ⊖ lit 6
        y1 = p1Y t ⊖ lit 6
        x2 = p2X t ⊖ lit 6
        y2 = p2Y t ⊖ lit 6
        bunch1 = put x1 y1 (disc (lit 6) (cls "stat rust"))
        bunch2 = put x2 y2 (disc (lit 6) (cls "stat rust"))
    in canvas (pipeRing ++ˡ (bunch1 ∷ bunch2 ∷ flashSparks t))

------------------------------------------------------------------------
-- Exported Diagrams and Animations

lhcFrameAt : ℕ → Dia ℕ
lhcFrameAt = PipeFrame.lhcDia natO

lhcTemplate : Dia (OExpr ⊤)
lhcTemplate = PipeFrame.lhcDia termO tO

-- Smooth parametric loop (~0.5s per loop with ms = 16)
lhcAnim : Anim
lhcAnim = tweenD period (+ 0 ℚ./ 1) (+ period ℚ./ 1) T.Linear lhcTemplate
