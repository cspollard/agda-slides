{-# OPTIONS --safe --without-K #-}

-- The LHC animation: a circular beam pipe viewed at an angle (an ellipse), two counter-circulating
-- proton bunches that collide at the bottom of the pipe, and a flash of sparks on the collision.
--
-- A scene of three layers, one lap of `period` ticks:
--
--   pipe     one leaf, an `ellipse` of radii `RX` `RY` (exact, drawn as an SVG `<ellipse>`), held for
--            the whole lap and styled by the CSS class `pipe`;
--   bunches  one frame per tick: the two bunches, at the angle `64 + 4 k` and its mirror image;
--   flash    the first 16 ticks only: a burst that grows for 8 ticks and shrinks for 8, and eight
--            sparks flying out.
--
-- The three are laid over each other with the scene's `∥` (`Slides.Scene.Syntax`, `∥ₛ` here), so the pipe is shipped
-- once, not once per frame.  The legacy version evaluated tables of positions as formulas in the
-- tick, because its scalars had a sine-less multiplication; here the scalars of a leaf are the
-- Space and Time terms, which have no product of two variables, so each frame is a diagram over
-- literals computed in whole numbers (`trig`, a 17-entry sine table with linear interpolation,
-- under 0.2 % off).  Both bunches meet at the bottom at tick 0 and pass each other at the top
-- at tick 32 (two beams in one pipe); only the meeting at the bottom flashes.

module Slides.Examples.LHC where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; map; foldr; applyUpTo; [_]) renaming (_++_ to _++ˡ_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _/_; _%_; _<ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String) renaming (_++_ to _++ˢ_)

open import Slides.Diagram.Convenience
open import Data.Container.FreeMonad using (pure)
open import Slides.Deck.Anim using (Anim; frame′; hold; ι; _⨾_; liftDia) renaming (_∥_ to _∥ₛ_)

------------------------------------------------------------------------
-- Dimensions and period

-- every length is in units of 1/K of the original size: whole numbers then round to a quarter of
-- what they did, so the bunches sit close to the pipe (the page scales the drawing to its width)
K : ℕ
K = 4

W H : ℕ
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

-- eight directions for the sparks, 45° apart
sparkDirs : List ((ℕ × Bool) × (ℕ × Bool))
sparkDirs = map (λ j → trig (32 * j)) (applyUpTo (λ j → j) 8)

------------------------------------------------------------------------
-- The layers, as diagrams over whole numbers

put : ℕ → ℕ → Dia ℕ → Dia ℕ
put = place W H

canvas : List (Dia ℕ) → Dia ℕ
canvas = layers W H

-- the pipe: an ellipse about (CX , CY), placed by the corner of its frame
pipe : Dia ℕ
pipe = canvas (put (CX ∸ RX) (CY ∸ RY) (ellipse RX RY (cls "pipe")) ∷ [])

-- a bunch at (x , y): a soft halo and a core
bunch : ℕ → ℕ → List (Dia ℕ)
bunch x y =
    put (x ∸ 11 * K) (y ∸ 11 * K) (disc (11 * K) (cls "halo"))
  ∷ put (x ∸ 7 * K) (y ∸ 7 * K) (disc (7 * K) (cls "bunch"))
  ∷ []

-- the two bunches at tick k: the first at angle 64 + 4 k, the second its mirror image in the
-- vertical axis
bunches : ℕ → Dia ℕ
bunches k = canvas (bunch (x₁ k) (y₁ k) ++ˡ bunch (2 * CX ∸ x₁ k) (y₁ k))
  where
    x₁ y₁ : ℕ → ℕ
    x₁ k = proj₁ (ellipseAt (64 + 4 * k))
    y₁ k = proj₂ (ellipseAt (64 + 4 * k))

-- the flash after the collision at tick 0: a burst that grows for 8 ticks and shrinks for 8,
-- and sparks that fly out for 16
burstR : ℕ → ℕ
burstR u = if u <ᵇ 8 then 3 * K * u else 3 * K * (16 ∸ u)

sparkD : ℕ → ℕ
sparkD u = 6 * K + 3 * K * u

sparkR : ℕ
sparkR = 3 * K

-- a spark flies from the collision point along (cos , sin), squashed to 60 % vertically
spark : ℕ → (ℕ × Bool) × (ℕ × Bool) → Dia ℕ
spark u ((cm , cn) , (sm , sn)) =
  let dx = cm * sparkD u / 10000
      dy = sm * 60 / 100 * sparkD u / 10000
      x  = if cn then CX ∸ dx else CX + dx
      y  = if sn then (CY + RY) ∸ dy else (CY + RY) + dy
  in put (x ∸ sparkR) (y ∸ sparkR) (disc sparkR (cls "spark"))

flash : ℕ → Dia ℕ
flash u =
  let r = burstR u
  in canvas (put (CX ∸ r) ((CY + RY) ∸ r) (disc r (cls "burst")) ∷ map (spark u) sparkDirs)

------------------------------------------------------------------------
-- The scene

-- `suc m` frames of `f` from tick `k`, one tick each
seqFrames : (ℕ → Dia ℕ) → ℕ → ℕ → Anim
seqFrames f k zero    = frame′ 1 (liftDia (f k))
seqFrames f k (suc m) = frame′ 1 (liftDia (f k)) ⨾ seqFrames f (suc k) m

-- a leaf present for the whole lap
whole : Dia ℕ → Anim
whole d = hold (ι period) (pure (liftDia d))

-- the static frame of a diagram at tick `k` (for tests and still images)
lhcFrameAt : ℕ → Dia ℕ
lhcFrameAt k = canvas (pipe ∷ bunches k ∷ (if k <ᵇ 16 then [ flash k ] else []))

-- one lap: the pipe all along, the bunches every tick, the flash in the first 16
lhcAnim : Anim
lhcAnim = whole pipe ∥ₛ seqFrames bunches 0 63 ∥ₛ seqFrames flash 0 15
