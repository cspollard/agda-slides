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
open import Data.List using (List; []; _∷_; map; foldr; applyUpTo; length; [_]) renaming (_++_ to _++ˡ_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _/_; _%_; _<ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Char using (Char)
open import Data.String using (String; toList; fromList) renaming (_++_ to _++ˢ_)

open import Slides.Diagram.Convenience
open import Slides.Diagram.TextMetrics using (textWidth)
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
H = 260 * K

-- ticks in one lap of a bunch
period : ℕ
period = 64

-- the ellipse: centre and radii
CX CY RX RY : ℕ
CX = 240 * K
CY = 125 * K
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

-- Captions: the diameter above the ring, the depth under its right side
caption : ℕ → ℕ → String → Dia ℕ
caption x y t = put (x ∸ textWidth fontC t / 2) y (text fontC t (cls "dim"))
  where fontC = 18 * K

captions : Dia ℕ
captions = canvas (caption CX (4 * K) "diameter: 27km" ∷ caption (370 * K) (H ∸ 36 * K) "100m underground" ∷ [])

-- The border through the ring (under it): a dashed curve, a smile of depth `bow`, lowest in the middle.
-- Its height at `x`, and its slope at `x` in degrees (small-angle: slope ≈ 2 bow d / RX², one
-- radian ≈ 57°), tilting the other way on the other side of the middle.
bow lineBase : ℕ
bow      = 45 * K
lineBase = 150 * K

dist : ℕ → ℕ
dist x = if x <ᵇ CX then CX ∸ x else x ∸ CX

lineY : ℕ → ℕ
lineY x = lineBase ∸ bow * (dist x * dist x) / (RX * RX)

tiltOf : ℕ → ℕ
tiltOf x = 57 * 2 * bow * dist x / (RX * RX)

border : Dia ℕ
border = put 0 0 (polyline (map pt (applyUpTo (λ i → i) 25)) (cls "border"))
  where pt : ℕ → ℕ × ℕ
        pt i = let x = 20 * i * K in x , lineY x

-- A word set along the curve: each letter is its own text, turned by the slope of the curve
-- under it (the CSS classes `tilt-l-n`, `tilt-r-n` rotate by 2n degrees), and sits a little
-- below the line.
advance letterSize : ℕ
advance    = 12 * K
letterSize = 20 * K

letter : Bool → ℕ → Char → Dia ℕ
letter below xc c =
  put (xc ∸ textWidth letterSize (fromList (c ∷ [])) / 2) ((if below then lineY xc + 26 * K else lineY xc ∸ 26 * K) ∸ letterSize * 3 / 4)
      (text letterSize (fromList (c ∷ [])) (cls ("dim tilt-" ++ˢ (if xc <ᵇ CX then "l-" else "r-") ++ˢ show (tiltOf xc / 2))))

word : Bool → ℕ → List Char → List (Dia ℕ)
word _     x []       = []
word below x (c ∷ cs) = letter below (x + advance / 2) c ∷ word below (x + advance) cs

-- France below the line on the left, Switzerland above it on the right, centred on a point of the curve
countries : Dia ℕ
countries = canvas (word true (centredAt 130 "France") (toList "France") ++ˡ word false (centredAt 350 "Switzerland") (toList "Switzerland"))
  where lenˢ : String → ℕ
        lenˢ t = length (toList t)
        centredAt : ℕ → String → ℕ
        centredAt c t = c * K ∸ (advance * lenˢ t) / 2

-- the pipe: an ellipse about (CX , CY), placed by the corner of its frame
pipe : Dia ℕ
pipe = canvas
  ( put (CX ∸ RX) (CY ∸ RY) (ellipse RX RY (cls "pipe"))
  ∷ border ∷ countries ∷ captions ∷ [] )

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

------------------------------------------------------------------------
-- The trigger pipeline: a collision seen along the beam, then three stages joined by arrows
--
-- One scene like the ring's: the static row (the empty slot the collision is drawn in, the
-- boxes, the arrows and their rates) held for the lap, and the collision over it, eight
-- tracks flying out of the vertex (twice in a lap, so the loop is seamless).

W2 H2 slotS gapW boxW boxH : ℕ
W2    = 1010 * K
H2    = 110 * K
slotS = 110 * K
gapW  = 100 * K
boxW  = 200 * K
boxH  = 80 * K

put2 : ℕ → ℕ → Dia ℕ → Dia ℕ
put2 = place W2 H2

canvas2 : List (Dia ℕ) → Dia ℕ
canvas2 = layers W2 H2

-- the gap between two stages: an arrow is drawn through it, and its rate sits underneath
gap : String → Dia ℕ
gap t = layers gapW H2 (place gapW H2 ((gapW ∸ textWidth (16 * K) t) / 2) (H2 / 2 + 8 * K) (text (16 * K) t (cls "dim")) ∷ [])

stage₂ : String → List String → Dia ℕ
stage₂ i ls = card i "node" 18 boxW boxH (lines (18 * K) ls defaultStyle)

pipelineRow : Dia ℕ
pipelineRow =
  hcat 0
    ( ("tc" ⦂ spacer slotS H2)
    ∷ gap "40 MHz"
    ∷ stage₂ "t1" ("FPGAs" ∷ "custom hardware" ∷ [])
    ∷ gap "1 kHz"
    ∷ stage₂ "t2" ("100,000 CPUs" ∷ [])
    ∷ gap "5 kHz"
    ∷ stage₂ "t3" ("hard disks" ∷ "and tape" ∷ [])
    ∷ [] )
  ▹[ cls "flow cy heavy" ] ("tc" ⟶ "t1" ∷ "t1" ⟶ "t2" ∷ "t2" ⟶ "t3" ∷ [])

-- the detector: a thin circle round the collision, in the slot
detector : Dia ℕ
detector = put2 (5 * K) (5 * K) (ellipse (50 * K) (50 * K) (cls "detector"))

staticPipeline : Dia ℕ
staticPipeline = canvas2 (put2 0 0 pipelineRow ∷ detector ∷ [])

-- the vertex at the middle of the slot
VX VY : ℕ
VX = slotS / 2
VY = H2 / 2

-- a point `d` from the vertex along a direction (cos , sin)
along : (ℕ × Bool) × (ℕ × Bool) → ℕ → ℕ × ℕ
along ((cm , cn) , (sm , sn)) d =
  let dx = cm * d / 10000
      dy = sm * d / 10000
  in (if cn then VX ∸ dx else VX + dx) , (if sn then VY ∸ dy else VY + dy)

-- eight tracks, 45° apart but not quite regularly
trackDirs : List ((ℕ × Bool) × (ℕ × Bool))
trackDirs = map (λ j → trig (32 * j + 8 + 5 * (j % 3))) (applyUpTo (λ j → j) 8)

-- a track after `u` ticks: a line from the vertex and a dot at its tip
track : ℕ → (ℕ × Bool) × (ℕ × Bool) → Dia ℕ
track u dir =
  let p = along dir (6 * K + (44 * K * u) / 31)
  in canvas2
       ( put2 (proj₁ p ∸ 3 * K) (proj₂ p ∸ 3 * K) (disc (3 * K) (cls "spark"))
       ∷ put2 0 0 (polyline ((VX , VY) ∷ p ∷ []) (cls "track"))
       ∷ [] )

collision : ℕ → Dia ℕ
collision k = canvas2 (put2 (VX ∸ 4 * K) (VY ∸ 4 * K) (disc (4 * K) (cls "burst")) ∷ map (track (k % 32)) trackDirs)

triggerAnim : Anim
triggerAnim = whole staticPipeline ∥ₛ seqFrames collision 0 63
