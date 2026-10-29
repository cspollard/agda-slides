{-# OPTIONS --safe --without-K #-}

-- The title animation: protons collide at the LHC and eight particles fly out and coalesce into a
-- long prism cut into eight blocks of different colours, one event's data summary, a tensor of
-- shape (1, 8).  Below it rests a static tensor of the same shape, the data accumulated so far;
-- the event's tensor drops onto it and merges with it (PAIRS), updating it (each block takes the
-- mean hue of the events so far), and at every merge the likelihood curve on the right gets
-- narrower.  Six events, then it loops from an empty accumulator.  At one tick a second it takes
-- five minutes.
--
-- Three layers over a 1000 × 320 canvas, 300 ticks each:
--
--   story   six cycles of fifty ticks, one per collision; each act of a cycle is one moving leaf
--           (`tween`), the positions following the driver `now`: a position moves by a percentage
--           of it (`pctOf`), so each particle's flight is a percentage of the same driver;
--   state   the accumulated tensor and the likelihood curve, which change together at the merges
--           (tick 46 of each cycle, 296 the last): seven stages;
--   beam    the beam line, static.
--
--   a cycle (50 ticks)
--     15  the protons approach along the beam
--     10  eight particles fly out to the eight places of the event's prism
--      5  the prism grows under them
--      5  the event's tensor at rest
--     12  it drops onto the accumulated tensor
--      3  merged: the accumulator and the curve have updated (at the first of these ticks)

module Slides.Examples.TitleAnim where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; map; upTo; _++_; foldr; concat; filterᵇ)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _/_; _%_; _⊓_; _<ᵇ_; _≤ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_)
open import Data.String using (String) renaming (_++_ to _++ˢ_)

open import Slides.Deck.Anim
  using ( Anim; Leaf; Sc; lit; now; _⊞_; _⊟_; pctOf; frame′; tween; Linear; ι; liftDia; sequence
        ; defaultStyle; filled; stroked ) renaming (_∥_ to _∥ₛ_)
open import Slides.Diagram.Style using (thick; dashed)
open import Slides.Diagram.Convenience using (Dia; layers; polyline; disc; cls; dim; place)
import Slides.Diagram.Syntax as D
open import Slides.Examples.Collider using (isqrt)

------------------------------------------------------------------------
-- The canvas and the places in it

tW tH : ℕ
tW = 1000
tH = 320

-- the collision point, on the beam at the top
CX CY : ℕ
CX = 270
CY = 60

-- a leaf of terms over the canvas, and a child of it at a point (its top-left corner)
canvasL : List Leaf → Leaf
canvasL = layers (lit tW) (lit tH)

at : Sc → Sc → Leaf → Leaf
at x y d = D.place (lit tW) (lit tH) x y d

absolute : Leaf → Leaf
absolute = at (lit 0) (lit 0)

-- a position that moves from `x₀` by `p` percent of the driver, up or left when `neg`
slide : ℕ → Bool → ℕ → Sc
slide x₀ neg p = if neg then lit x₀ ⊟ pctOf p now else lit x₀ ⊞ pctOf p now

-- the distance between two numbers
dist : ℕ → ℕ → ℕ
dist x y = (x ∸ y) + (y ∸ x)

------------------------------------------------------------------------
-- The tensors: prisms of eight blocks

segW segH depthX depthY prismX eventY accY : ℕ
segW   = 46     -- a block's width
segH   = 26     -- its height
depthX = 14     -- the prism's depth, drawn obliquely: right ...
depthY = 12     -- ... and up
prismX = 90     -- the left end of a prism
eventY = 165    -- the top of the event's prism
accY   = 265    -- the top of the accumulator

-- the colours of event j: a hue for each of the eight blocks (pseudo-random but fixed)
eventHue : ℕ → ℕ → ℕ
eventHue j i = (j * 97 + i * 61 + 13 * (i + 2) * (j + 3)) % 360

-- the hue of block i of the accumulator after k events: the mean of the events' hues
accHue : ℕ → ℕ → ℕ
accHue zero    i = 0
accHue (suc k) i = foldr _+_ 0 (map (λ j → eventHue j i) (upTo (suc k))) / suc k

hsl : ℕ → ℕ → String
hsl h l = "hsl(" ++ˢ show h ++ˢ ",65%," ++ˢ show l ++ˢ "%)"

-- a face of a prism: a polygon in a colour, edged in white
face : List (Sc × Sc) → String → Leaf
face ps c = absolute (D.polygon ps (filled c (stroked "#fff" (thick 1 defaultStyle))))

-- block i of a prism whose front face has its top-left corner at (x , y), of height h, in a hue;
-- the last block shows its end
block : ℕ → Bool → Sc → Sc → ℕ → List Leaf
block i last y h hue = end ++ top ∷ front ∷ []
  where
    x₀ = prismX + segW * i
    x₁ = x₀ + segW
    front top : Leaf
    front = face ((lit x₀ , y) ∷ (lit x₁ , y) ∷ (lit x₁ , y ⊞ h) ∷ (lit x₀ , y ⊞ h) ∷ []) (hsl hue 52)
    top   = face ((lit x₀ , y) ∷ (lit x₁ , y) ∷ (lit (x₁ + depthX) , y ⊟ lit depthY) ∷ (lit (x₀ + depthX) , y ⊟ lit depthY) ∷ []) (hsl hue 68)
    end : List Leaf
    end = if last
      then face ((lit x₁ , y) ∷ (lit (x₁ + depthX) , y ⊟ lit depthY) ∷ (lit (x₁ + depthX) , (y ⊟ lit depthY) ⊞ h) ∷ (lit x₁ , y ⊞ h) ∷ []) (hsl hue 38) ∷ []
      else []

-- a prism: its eight blocks in the hues `hue i`
prism : (ℕ → ℕ) → Sc → Sc → List Leaf
prism hue y h = concat (map (λ i → block i (i ≡ᵇ 7) y h (hue i)) (upTo 8))
  where open import Data.Nat using (_≡ᵇ_)

-- an empty accumulator: the outline of a prism
ghost : Leaf
ghost = canvasL
  ( absolute (D.polygon (map (λ { (x , y) → lit x , lit y })
        ((prismX , accY) ∷ (prismX + 8 * segW , accY) ∷ (prismX + 8 * segW , accY + segH) ∷ (prismX , accY + segH) ∷ []))
        (stroked "#b0b0b0" (dashed "10 8" (thick 3 defaultStyle))))
  ∷ [] )

-- the accumulator after k events
accumulator : ℕ → Leaf
accumulator zero    = ghost
accumulator (suc k) = canvasL (prism (accHue (suc k)) (lit accY) (lit segH))

-- the beam
beam : Leaf
beam = canvasL (absolute (D.polyline ((lit 20 , lit CY) ∷ (lit 520 , lit CY) ∷ []) (cls "beam")) ∷ [])

------------------------------------------------------------------------
-- The acts of a collision

-- the middle of block i of the event's prism, where particle i comes to rest
landX landY : ℕ → ℕ
landX i = prismX + segW * i + segW / 2
landY _ = eventY + segH / 2

-- a disc of radius r centred at a point of terms
ball : String → ℕ → Sc → Sc → Leaf
ball c r x y = at (x ⊟ lit r) (y ⊟ lit r) (D.disc (lit r) (cls c))

-- the protons approach; each moves by the driver, 0 to 210
protons : Anim
protons = tween Linear (ι 0) (ι 210) (ι 15)
  (canvasL ( ball "bunch" 10 (lit 60 ⊞ now) (lit CY) ∷ ball "bunch" 10 (lit 480 ⊟ now) (lit CY) ∷ [] ))

-- eight particles fly from the collision to the places of the prism: the driver goes 0 to 100, and
-- each moves by its horizontal distance and the drop, in percent of it
flyOut : Anim
flyOut = tween Linear (ι 0) (ι 100) (ι 10)
  (canvasL (map (λ i → ball "spark" 6 (slide CX (landX i <ᵇ CX) (dist (landX i) CX)) (slide CY false (landY i ∸ CY))) (upTo 8)))

landed : List Leaf
landed = map (λ i → ball "spark" 6 (lit (landX i)) (lit (landY i))) (upTo 8)

-- the prism grows under the particles, height 0 to segH
growPrism : ℕ → Anim
growPrism j = tween Linear (ι 0) (ι segH) (ι 5) (canvasL (prism (eventHue j) (lit eventY) now ++ landed))

-- the event's tensor at rest, then dropping onto the accumulator (the driver 0 to 100)
rest : ℕ → Anim
rest j = frame′ 5 (canvasL (prism (eventHue j) (lit eventY) (lit segH)))

drop : ℕ → Anim
drop j = tween Linear (ι 0) (ι (accY ∸ eventY)) (ι 12) (canvasL (prism (eventHue j) (lit eventY ⊞ now) (lit segH)))

merged : Anim
merged = frame′ 3 (canvasL [])

-- one collision, fifty ticks
collision : ℕ → Anim
collision j = sequence (protons ∷ flyOut ∷ growPrism j ∷ rest j ∷ drop j ∷ merged ∷ [])

story : Anim
story = sequence (map collision (upTo 6))

beamLayer : Anim
beamLayer = frame′ 300 beam

------------------------------------------------------------------------
-- The state: the accumulated tensor and the likelihood curve

-- the plot's frame, on the right: x from 620 to 980, the curve's minimum at the middle
plotL plotMid plotTop plotMin plotBase : ℕ
plotL    = 620
plotMid  = 800
plotTop  = 55
plotMin  = 245
plotBase = 275

-- the steepness (tenths) of the curve after k events: wide at first, then narrower with each
steepness : ℕ → ℕ
steepness k = 2 + k * (k + 3)

-- the curve is sampled every 3 units: 121 points over 360, the minimum at the 60th.  Step i is
-- (i − 60)/4 of the old unit steps, so its height above the minimum is a (i − 60)² / 160 tenths
rise : ℕ → ℕ → ℕ
rise a i = a * (sq (dist i 60)) / 160
  where
    sq : ℕ → ℕ
    sq n = n * n

-- the curve stops where it leaves the top of the plot, instead of running along it
visible : ℕ → ℕ → Bool
visible a i = rise a i ≤ᵇ (plotMin ∸ plotTop)

curvePoints : ℕ → List (ℕ × ℕ)
curvePoints a = map (λ i → plotL + 3 * i , plotMin ∸ rise a i) (filterᵇ (visible a) (upTo 121))

-- the curve after k events, with a bar across it at a fixed level (its width is the uncertainty)
curveFrame : ℕ → Dia ℕ
curveFrame k =
  layers tW tH
    ( place tW tH 0 0 (polyline (curvePoints a) (cls "curve"))
    ∷ place tW tH 0 0 (polyline ((plotMid ∸ 12 * w , barY) ∷ (plotMid + 12 * w , barY) ∷ []) (cls "interval"))
    ∷ place tW tH 0 0 (polyline ((plotL , plotTop) ∷ (plotL , plotBase) ∷ (plotL + 360 , plotBase) ∷ []) (cls "axis"))
    ∷ place tW tH (plotMid ∸ 8) (plotBase + 2) (dim 22 "μ")
    ∷ place tW tH (plotL + 10) 5 (dim 22 "−2 ln L")
    ∷ [] )
  where
    a = steepness k
    barY = plotMin ∸ 30
    w = isqrt (300 / a) ⊓ 15

-- how long stage k lasts: the first up to the first merge (tick 46), the last from the sixth (296)
stageTicks : ℕ → ℕ
stageTicks 0 = 46
stageTicks 6 = 4
stageTicks _ = 50

stage : ℕ → Anim
stage k = frame′ (stageTicks k) (canvasL (absolute (liftDia′ (curveFrame k)) ∷ accumulator k ∷ []))
  where liftDia′ : Dia ℕ → Leaf
        liftDia′ = liftDia

stateLayer : Anim
stateLayer = sequence (map stage (upTo 7))

------------------------------------------------------------------------
-- The whole

titleAnim : Anim
titleAnim = beamLayer ∥ₛ story ∥ₛ stateLayer
