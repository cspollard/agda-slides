{-# OPTIONS --safe --without-K #-}

-- A very simplified ATLAS, in the plane transverse to the beam: a cutaway of the concentric
-- subdetectors, off-centre in its frame to leave room for a legend.
--
--   inner tracker   silicon layers (thin rings) inside a disc, wrapped by the solenoid
--   calorimetry     an electromagnetic ring of fine cells, a hadronic ring of coarse ones
--   muon system     three stations of chambers
--
-- A wedge of the upper right is cut away, deeper for each layer going in (a staircase), so that
-- every layer shows its outer face.  An event is drawn over it: a jet (three tracks, a cluster
-- of lit cells in both calorimeters), an electron (one track, an electromagnetic cluster), a
-- photon (the same without a track, dashed), and a muon that crosses the whole detector, leaving
-- a minimum-ionising trace in both calorimeters and a hit in every station.
--
-- Everything is a diagram over whole numbers.  An angle is a number of 1/1024 turns, measured
-- from the right and growing clockwise on the page (y grows downwards); `ptAt r a` is the point
-- at radius `r` and angle `a` about the centre.  The sine is `Slides.Examples.LHC`'s table, a
-- little finer in the interpolation.
--
-- The look is a `Theme` (the background and every colour): `dark` is the default, `light` a
-- light page, and `withBackground c T` any other background.  `Parts T` has the pieces of the
-- picture in that theme, each a list of layers (the topmost first) or a single layer, so they
-- can be taken or left out as needed:
--
--   background  tracker  detector (the quiet cells)  eventCells (the cells with the event lit)
--   jet  electron  muon  photon  vertex      the particles
--   legend  heading                           the text
--   scene layers                              a diagram of layers laid over the background
--
-- and `atlasOn T` is all of them.  For example, the detector alone on white:
--
--   open Parts (withBackground "#ffffff" light)
--   bare = scene (tracker ++ detector)

module Slides.Examples.ATLAS where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; map; reverse; applyUpTo; concat; _++_)
open import Data.Nat using (ℕ; suc; _+_; _*_; _∸_; _/_; _%_; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)

open import Slides.Diagram.Convenience
open import Slides.Diagram.Style using (filled; stroked; thick; faded; dashed)
open import Slides.Examples.LHC using (sinTable; nth; lifted)

------------------------------------------------------------------------
-- The frame and the centre of the detector

W H CX CY : ℕ
W  = 1080
H  = 700
CX = 380
CY = 350

put : ℕ → ℕ → Dia ℕ → Dia ℕ
put = place W H

canvas : List (Dia ℕ) → Dia ℕ
canvas = layers W H

------------------------------------------------------------------------
-- Trigonometry: angles in 1/1024 turns

-- sin of a first-quadrant angle (a ≤ 256), interpolated between the 17 table entries
sinQ : ℕ → ℕ
sinQ a = lo + ((hi ∸ lo) * (a % 16)) / 16
  where lo = nth (a / 16) sinTable
        hi = nth (suc (a / 16)) sinTable

-- (cos , sin) as a magnitude in tenthousandths and a flag that it is negative
trig : ℕ → (ℕ × Bool) × (ℕ × Bool)
trig a = quad ((a / 256) % 4) (a % 256)
  where
    quad : ℕ → ℕ → (ℕ × Bool) × (ℕ × Bool)
    quad 0 r = (sinQ (256 ∸ r) , false) , (sinQ r , false)
    quad 1 r = (sinQ r , true)          , (sinQ (256 ∸ r) , false)
    quad 2 r = (sinQ (256 ∸ r) , true)  , (sinQ r , true)
    quad _ r = (sinQ r , false)         , (sinQ (256 ∸ r) , true)

-- the point at radius r and angle a about the centre, to the nearest unit
ptAt : ℕ → ℕ → ℕ × ℕ
ptAt r a =
    (((CX * 10000 + r * lifted (proj₁ t)) ∸ r * 10000) + 5000) / 10000
  , (((CY * 10000 + r * lifted (proj₂ t)) ∸ r * 10000) + 5000) / 10000
  where t = trig a

------------------------------------------------------------------------
-- Themes

record Theme : Set where
  field
    bg gap                : String   -- the page, and the lines between cells and round hits
    trackerFill silicon coil : String
    ecalBase ecalLit hcalBase hcalLit muBase muLit : String
    track hit muonColour   : String
    ink subtle                : String   -- the text, and its secondary lines

dark light : Theme
dark = record
  { bg = "#151b26" ; gap = "#151b26"
  ; trackerFill = "#1d2635" ; silicon = "#6e809b" ; coil = "#d9c089"
  ; ecalBase = "#2a4642" ; ecalLit = "#9fe3c4"
  ; hcalBase = "#35385a" ; hcalLit = "#f1b98f"
  ; muBase = "#2b3e5e"   ; muLit = "#8fc4f2"
  ; track = "#e6ebf4" ; hit = "#f6e6a3" ; muonColour = "#f28f9b"
  ; ink = "#d3dae6" ; subtle = "#8794a8" }
light = record
  { bg = "#f5f6f9" ; gap = "#f5f6f9"
  ; trackerFill = "#e6eaf1" ; silicon = "#8a97ab" ; coil = "#c9a85a"
  ; ecalBase = "#cfe5de" ; ecalLit = "#3fae85"
  ; hcalBase = "#dcdcee" ; hcalLit = "#e08c55"
  ; muBase = "#d5e0f0"   ; muLit = "#4f95d6"
  ; track = "#2f3846" ; hit = "#d9a93a" ; muonColour = "#e0606f"
  ; ink = "#2c3442" ; subtle = "#7d8799" }

-- the same theme on another background (any CSS colour, `none` for the page's own)
withBackground : String → Theme → Theme
withBackground c T = record T { bg = c ; gap = c }

-- a filled shape with an outline, at an opacity in percent
paint : String → String → ℕ → ℕ → Style
paint f s w o = faded o (thick w (stroked s (filled f defaultStyle)))

line : String → ℕ → Style
line c w = thick w (stroked c defaultStyle)

------------------------------------------------------------------------
-- Geometry that does not depend on the theme

-- the points of the arc at radius r from angle a for w, a point every 8
arcPts : ℕ → ℕ → ℕ → List (ℕ × ℕ)
arcPts r a w = map (λ j → ptAt r (a + 8 * j)) (applyUpTo (λ j → j) (suc (w / 8)))

-- the cell between the radii r0 < r1, from angle a for w
cell : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ)
cell r0 r1 a w = arcPts r1 a w ++ reverse (arcPts r0 a w)

-- how much of a cell is lit: 0 (not), then 1 … 3 (brightest); a list of (cell start , level)
level : List (ℕ × ℕ) → ℕ → ℕ
level []             a = 0
level ((b , n) ∷ ls) a = if b ≡ᵇ a then n else level ls a

glow : ℕ → ℕ
glow l = if l ≡ᵇ 1 then 45 else if l ≡ᵇ 2 then 72 else 100

-- the angle at radius r of a track that starts at angle φ and has bent by `b` at radius 340,
-- clockwise or not (`neg`)
bendAt : ℕ → Bool → ℕ → ℕ → ℕ
bendAt φ neg b r = if neg then (φ + 1024) ∸ δ else φ + δ
  where δ = b * r / 340

trackPt : ℕ → Bool → ℕ → ℕ → ℕ × ℕ
trackPt φ neg b r = ptAt r (bendAt φ neg b r)

-- a track out to radius rEnd (a multiple of 24), as a curve of segments 24 long
trackLine : ℕ → Bool → ℕ → ℕ → Style → Dia ℕ
trackLine φ neg b rEnd s =
  put 0 0 (polyline (map (trackPt φ neg b) (applyUpTo (λ j → 24 * j) (suc (rEnd / 24)))) s)

dot : ℕ → ℕ × ℕ → Style → Dia ℕ
dot r (x , y) s = put (x ∸ r) (y ∸ r) (disc r s)

-- A disc of radius r about the centre
discAt : ℕ → Style → Dia ℕ
discAt r = dot r (CX , CY)

-- the radii of the silicon layers, and of the muon stations' middles
siliconR stationR : List ℕ
siliconR = 24 ∷ 40 ∷ 58 ∷ 78 ∷ 94 ∷ []
stationR = 250 ∷ 286 ∷ 322 ∷ []

-- the lit cells, by the angle of their start
ecalLits hcalLits muLits : List (ℕ × ℕ)
ecalLits = (624 , 1) ∷ (640 , 3) ∷ (656 , 3) ∷ (672 , 2) ∷ (688 , 2) ∷ (704 , 1)   -- jet
         ∷ (320 , 1) ∷ (336 , 3) ∷ (352 , 2)                                         -- electron
         ∷ (128 , 1) ∷ (144 , 3) ∷ (160 , 2)                                         -- photon
         ∷ (16 , 1) ∷ []                                                             -- muon
hcalLits = (608 , 1) ∷ (640 , 3) ∷ (672 , 2) ∷ (0 , 1) ∷ []
muLits   = (0 , 3) ∷ []

------------------------------------------------------------------------
-- The pieces, in a theme

module Parts (T : Theme) where
  open Theme T

  -- the page, rounded
  background : Dia ℕ
  background = put 0 0 (rectangle W H (rounded 22 (paint bg bg 1 100)))

  -- `n` cells of width w from angle `hi` on, between the radii; the lit ones in `litC`
  ringCells : (r0 r1 hi w n : ℕ) (base litC : String) → List (ℕ × ℕ) → List (Dia ℕ)
  ringCells r0 r1 hi w n base litC lits = map one (applyUpTo (λ j → hi + w * j) n)
    where
      one : ℕ → Dia ℕ
      one a = put 0 0 (polygon (cell r0 r1 a w) (style (level lits (a % 1024))))
        where style : ℕ → Style
              style 0 = paint base gap 1 100
              style l = paint litC gap 1 (glow l)

  -- inside out: silicon layers, tracker, solenoid
  tracker : List (Dia ℕ)
  tracker =
      map (λ r → discAt r (faded 70 (thick 1 (stroked silicon defaultStyle)))) siliconR
    ++ discAt 100 (paint trackerFill silicon 1 100)
    ∷ discAt 106 (paint coil coil 1 100)
    ∷ []

  -- The calorimeters and the muon stations, as cells from the cut's far gap round to its near
  -- gap; the cut of a layer is [lo , hi] and the staircase deepens towards the centre of the
  -- cut, at 896.  The lit cells are the arguments (none: the quiet detector).
  cellsWith : (ecalL hcalL muL : List (ℕ × ℕ)) → List (Dia ℕ)
  cellsWith ecalL hcalL muL =
       ringCells 112 148 960 16 56 ecalBase ecalLit ecalL
    ++ ringCells 152 222 992 32 26 hcalBase hcalLit hcalL
    ++ ringCells 244 256 0 32 24 muBase muLit muL
    ++ ringCells 280 292 0 32 24 muBase muLit muL
    ++ ringCells 316 328 0 32 24 muBase muLit muL

  -- the cells with nothing lit, and with the event's clusters lit
  detector eventCells : List (Dia ℕ)
  detector   = cellsWith [] [] []
  eventCells = cellsWith ecalLits hcalLits muLits

  -- a hit of radius hr on the track at each of the radii
  hitsAt : ℕ → Bool → ℕ → ℕ → List ℕ → String → List (Dia ℕ)
  hitsAt φ neg b hr rs c = map (λ r → dot hr (trackPt φ neg b r) (paint c gap 1 100)) rs

  -- a charged track: the curve, with a hit in every silicon layer
  charged : ℕ → Bool → ℕ → ℕ → List (Dia ℕ)
  charged φ neg b rEnd = hitsAt φ neg b 4 siliconR hit ++ trackLine φ neg b rEnd (line track 2) ∷ []

  -- the jet (three tracks, ending in the hadronic calorimeter), an electron, a muon that leaves
  -- the detector, and a photon (no track, only a dashed line to the calorimeter)
  jet electron muon photon : List (Dia ℕ)
  jet      = charged 632 false 36 216 ++ charged 652 false 20 216 ++ charged 668 false 50 216
  electron = charged 360 true 30 144
  muon     = hitsAt 24 true 12 5 stationR muonColour
          ++ hitsAt 24 true 12 4 siliconR hit
          ++ trackLine 24 true 12 360 (line muonColour 3) ∷ []
  photon   = trackLine 150 false 0 144 (dashed "6 5" (line ecalLit 2)) ∷ []

  -- the collision point
  vertex : Dia ℕ
  vertex = dot 3 (CX , CY) (paint hit gap 1 100)

  -- the legend and the title, at the right
  swatch : String → Dia ℕ
  swatch c = disc 6 (paint c c 1 100)

  entry : String → String → Dia ℕ
  entry c l = hcat 12 (swatch c ∷ text 17 l (filled ink defaultStyle) ∷ [])

  legend heading : Dia ℕ
  legend = put 790 210 (vcatA left 16
    ( entry silicon "Inner tracker"
    ∷ entry coil "Solenoid"
    ∷ entry ecalLit "EM calorimeter"
    ∷ entry hcalLit "Hadronic calorimeter"
    ∷ entry muLit "Muon spectrometer"
    ∷ entry track "Charged track"
    ∷ entry muonColour "Muon"
    ∷ []))
  heading = put 790 90 (vcatA left 4
    ( bold 34 "ATLAS" (filled ink defaultStyle)
    ∷ text 15 "simplified, transverse view" (filled subtle defaultStyle)
    ∷ []))

  -- layers laid over the background, the topmost first
  scene : List (Dia ℕ) → Dia ℕ
  scene ls = canvas (ls ++ background ∷ [])

  -- everything
  atlas : Dia ℕ
  atlas = scene
    ( legend ∷ heading ∷ vertex
    ∷ muon ++ electron ++ jet ++ photon
    ++ tracker ++ eventCells )

atlasOn : Theme → Dia ℕ
atlasOn T = Parts.atlas T

-- the default: the dark theme
atlas : Dia ℕ
atlas = atlasOn dark
