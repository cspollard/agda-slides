{-# OPTIONS --safe --without-K #-}

-- A very simplified ATLAS: a cutaway of the concentric subdetectors, a cylinder along the beam,
-- off-centre in its frame to leave room for a legend.
--
--   inner tracker   silicon layers (thin rings) inside a disc, wrapped by the solenoid
--   calorimetry     an electromagnetic ring of fine cells, a hadronic ring of coarse ones
--   muon system     three stations of chambers
--
-- A wedge of the upper right is cut away along the beam, deeper for each layer going in (a
-- staircase), so that every layer shows its outer face.  An event is drawn over it: a jet
-- (three tracks, a cluster of lit cells in both calorimeters), an electron (one track, an
-- electromagnetic cluster), a photon (the same without a track, dashed), and a muon that crosses
-- the whole detector, leaving a minimum-ionising trace in both calorimeters and a hit in every
-- station.
--
-- Everything is a diagram over whole numbers, drawn by `Slides.Three`: a point of the detector is (r , a , z),
-- seen in a `View`; the cells are annular sectors (`Solid`s), painted back to front by `render`.
-- The view `flat` looks down the beam: the cylinder is a set of rings, the transverse plane.  Each
-- layer is drawn as its end face (a ring of cells), the outer surface of its cells and the walls
-- the cut leaves; the event goes over all of these, as if the detector were transparent.
--
-- The look is a `Theme` (the background and every colour): `dark` is the default, `light` a
-- light page, and `withBackground c T` any other background.  `Parts T V` has the pieces of the
-- picture in that theme and view, each a list of layers (the topmost first) or a single layer,
-- so they can be taken or left out as needed:
--
--   background                                  the page
--   detector  clusters                          the quiet cells with their tracker; the same with the lit cells
--   jet  electron  muon  photon  vertex         the particles
--   legend  heading                             the text
--   scene layers                                a diagram of layers laid over the background
--
-- and `atlasIn V T` is all of them (`atlas`: light and flat, `atlasTurned`: light and turned a
-- little).  For example, the detector and the muon alone on white, a little turned:
--
--   open Parts (withBackground "#ffffff" light) turned
--   bare = scene (muon ++ detector)

module Slides.Examples.ATLAS where

open import Data.Container.FreeMonad using (impure)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Integer using (ℤ; +_) renaming (_*_ to _*ᶻ_; -_ to negᶻ)
open import Data.Rational.Unnormalised using (ℚᵘ; mkℚᵘ; 0ℚᵘ; 1ℚᵘ; -_)
open import Data.List using (List; []; _∷_; map; applyUpTo; concatMap; _++_)
open import Data.Nat using (ℕ; suc; _+_; _*_; _∸_; _/_; _%_; _<ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)

open import Slides.Diagram.Convenience
open import Slides.Diagram.Style using (filled; stroked; thick; faded; dashed; anchored)
open import Slides.Text using (parse)
open import Slides.Trig using (fromℕ)
open import Slides.Three.Point
open import Slides.Three.View
open import Slides.Three.Solid
open import Slides.Three.Render

------------------------------------------------------------------------
-- The frame and the centre of the detector

W H CX CY : ℕ
W  = 1080
H  = 700
CX = 380
CY = 350

-- half the length of the barrel, in units
half : ℕ
half = 180

-- an angle in 1/1024 turns, as turns
turns : ℕ → ℚᵘ
turns a = mkℚᵘ (+ a) 1023

-- the order of the polynomials that place the cells (5: within 3·10⁻⁴, a third of a pixel at this size)
order : ℕ
order = 5

put : ℕ → ℕ → Dia ℕ → Dia ℕ
put = place W H

canvas : List (Dia ℕ) → Dia ℕ
canvas = layers W H

------------------------------------------------------------------------
-- Themes

record Theme : Set where
  field
    bg gap                 : String   -- the page, and the lines between cells and round hits
    trackerFill silicon coil : String
    ecalBase ecalLit hcalBase hcalLit muBase muLit : String
    track hit muonColour   : String
    ink subtle             : String   -- the text, and its secondary lines

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
-- What does not depend on the theme or the view

-- how much of a cell is lit, 1 … 3 (brightest), as an opacity in percent
glow : ℕ → ℕ
glow 1 = 45
glow 2 = 72
glow _ = 100

-- the angle at radius r of a track that starts at angle φ and has bent by `b` at radius 340,
-- clockwise or not (`neg`)
bendAt : ℕ → Bool → ℕ → ℕ → ℕ
bendAt φ neg b r = if neg then (φ + 1024) ∸ δ else φ + δ
  where δ = b * r / 340

dot : ℕ → ℕ × ℕ → Style → Dia ℕ
dot r (x , y) s = put (x ∸ r) (y ∸ r) (disc r s)

-- the radii of the silicon layers, and of the muon stations' middles
siliconR stationR : List ℕ
siliconR = 24 ∷ 40 ∷ 58 ∷ 78 ∷ 94 ∷ []
stationR = 250 ∷ 286 ∷ 322 ∷ []

-- a layer: cells between the radii r₀ and r₁, `n` of them of width `w` from angle `hi` on (all
-- the way round, or up to the cut), with their colour and the colour of their outlines (`none`:
-- no outline), and the lit ones.  A lit cell is (start angle , level 1 … 3); the whole volume of
-- the cell lights up.
Lit : Set
Lit = ℕ × ℕ

record Layer : Set where
  constructor layer
  field
    r₀ r₁ hi w n : ℕ
    fill rim litC : String
    lits : List Lit

------------------------------------------------------------------------
-- The pieces, in a theme and a view

module Parts (T : Theme) (V : View) where
  open Theme T

  -- the point at radius r, angle a (in 1/1024 turns) and z, and where it is on the page
  spot : ℕ → ℕ → ℚᵘ → Point
  spot r a z = cyl order (fromℕ r) (turns a) z

  pt : ℕ → ℕ → ℚᵘ → ℕ × ℕ
  pt r a z = project CX CY V (spot r a z)

  end : ℚᵘ
  end = fromℕ half

  -- the page, rounded
  background : Dia ℕ
  background = put 0 0 (rectangle W H (rounded 22 (paint bg bg 1 100)))

  ----------------------------------------------------------------------
  -- The layers, inside out

  layers′ : List Layer
  layers′ =
      layer 0   100 0   64 16 trackerFill "none" silicon []
    ∷ layer 100 106 0   64 16 coil        "none" coil    []
    ∷ layer 112 148 960 16 56 ecalBase ecalLit ecalLit ecalLits
    ∷ layer 152 222 992 32 26 hcalBase hcalLit hcalLit hcalLits
    ∷ layer 244 256 0   32 24 muBase   muLit   muLit   muLits
    ∷ layer 280 292 0   32 24 muBase   muLit   muLit   muLits
    ∷ layer 316 328 0   32 24 muBase   muLit   muLit   muLits
    ∷ []
    where
      -- the lit cells: the jet, the electron, the photon, and the muon (which also leaves a trace
      -- in the hadronic calorimeter and the stations)
      ecalLits hcalLits muLits : List Lit
      ecalLits = (624 , 1) ∷ (640 , 3) ∷ (656 , 3) ∷ (672 , 2) ∷ (688 , 2) ∷ (704 , 1)   -- jet
               ∷ (320 , 1) ∷ (336 , 3) ∷ (352 , 2)                                         -- electron
               ∷ (128 , 1) ∷ (144 , 3) ∷ (160 , 2)                                         -- photon
               ∷ (16 , 1) ∷ []                                                             -- muon
      hcalLits = (608 , 1) ∷ (640 , 3) ∷ (672 , 2) ∷ (0 , 1) ∷ []
      muLits   = (0 , 3) ∷ []

  -- the start angles of the cells of a layer
  starts : Layer → List ℕ
  starts (layer _ _ hi w n _ _ _ _) = applyUpTo (λ j → hi + w * j) n

  -- the cells of a layer, and the walls the cut leaves.  Their fill is faint enough to see the far
  -- side through the near one.
  layerSolids : Layer → List Solid
  layerSolids L = walls ++ map (λ a → xray (sector order (w / 8) r₀′ r₁′ (turns a) (turns w) (- end) end)) (starts L)
    where
      open Layer L
      r₀′ = fromℕ r₀
      r₁′ = fromℕ r₁
      xray = solid (mat fill rim 30) false
      lo : ℕ
      lo = (hi + n * w) % 1024
      wallAt : ℕ → Solid
      wallAt a = xray (wall order r₀′ r₁′ (turns a) (- end) end ∷ [])
      walls = if 1024 <ᵇ n * w + 1 then [] else wallAt lo ∷ wallAt hi ∷ []

  -- the lit cells of a layer, whole volumes
  litSolids : Layer → List Solid
  litSolids L = map (λ { (a , l) → solid (mat litC litC (glow l * 38 / 100)) false
                           (annularSector order (w / 8) (fromℕ r₀) (fromℕ r₁) (turns a) (turns w) (- end) end) }) lits
    where open Layer L

  -- the silicon layers: rings round the end face of the tracker
  silicons : List (Dia ℕ)
  silicons = map (λ r → put 0 0 (polygon (map (project CX CY V) (arc order 128 (fromℕ r) 0ℚᵘ 1ℚᵘ end)) (faded 70 (thick 1 (stroked silicon defaultStyle))))) (siliconR ++ 100 ∷ [])

  -- the detector: the silicon layers over every face of every layer, the nearest on top.  With the
  -- lit cells, each goes in its place among them, so whatever lies in front of a lit cell (the
  -- tracker, the solenoid, the layers outside) shows over it.
  stack : Bool → List (Dia ℕ)
  stack lit? = silicons ++ render W H CX CY V
    (concatMap layerSolids layers′ ++ (if lit? then concatMap litSolids layers′ else []))

  -- the quiet cells with their tracker, and the same with the lit cells (the clusters)
  detector clusters : List (Dia ℕ)
  detector = stack false
  clusters = stack true

  ----------------------------------------------------------------------
  -- The particles

  trackPt : ℕ → Bool → ℕ → ℤ → ℕ → ℕ × ℕ
  trackPt φ neg b s r = pt r (bendAt φ neg b r) (mkℚᵘ (s *ᶻ + r) 99)

  -- a track out to radius rEnd (a multiple of 24), as a curve of segments 24 long; it goes along
  -- the beam by `s` percent of its radius
  trackLine : ℕ → Bool → ℕ → ℤ → ℕ → Style → Dia ℕ
  trackLine φ neg b s rEnd st =
    put 0 0 (polyline (map (trackPt φ neg b s) (applyUpTo (λ j → 24 * j) (suc (rEnd / 24)))) st)

  -- a hit of radius hr on the track at each of the radii
  hitsAt : ℕ → Bool → ℕ → ℤ → ℕ → List ℕ → String → List (Dia ℕ)
  hitsAt φ neg b s hr rs c = map (λ r → dot hr (trackPt φ neg b s r) (paint c gap 1 100)) rs

  -- a charged track: the curve, with a hit in every silicon layer
  charged : ℕ → Bool → ℕ → ℤ → ℕ → List (Dia ℕ)
  charged φ neg b s rEnd = hitsAt φ neg b s 4 siliconR hit ++ trackLine φ neg b s rEnd (line track 2) ∷ []

  -- the jet (three tracks, ending in the hadronic calorimeter), an electron, a muon that leaves
  -- the detector, and a photon (no track, only a dashed line to the calorimeter)
  jet electron muon photon : List (Dia ℕ)
  jet      = charged 632 false 36 (+ 18) 216 ++ charged 652 false 20 (+ 22) 216
          ++ charged 668 false 50 (+ 26) 216
  electron = charged 360 true 30 (negᶻ (+ 30)) 144
  muon     = hitsAt 24 true 12 (+ 25) 5 stationR muonColour
          ++ hitsAt 24 true 12 (+ 25) 4 siliconR hit
          ++ trackLine 24 true 12 (+ 25) 360 (line muonColour 3) ∷ []
  photon   = trackLine 150 false 0 (+ 10) 144 (dashed "6 5" (line ecalLit 2)) ∷ []

  -- the collision point
  vertex : Dia ℕ
  vertex = dot 3 (CX , CY) (paint hit gap 1 100)

  ----------------------------------------------------------------------
  -- The legend and the title, at the right

  -- a line of text that starts at its frame's left edge: the frame has no width, so the text does
  -- not depend on the width the page's font gives it
  label : ℕ → String → Style → Dia ℕ
  label size t st = impure (Text 0 (size * 3 / 2) size (parse t) (anchored "start" st) , λ ())

  swatch : String → Dia ℕ
  swatch c = disc 9 (paint c c 1 100)

  entry : String → String → Dia ℕ
  entry c l = hcat 16 (swatch c ∷ label 26 l (filled ink defaultStyle) ∷ [])

  legend heading : Dia ℕ
  legend = put 780 200 (vcatA left 20
    ( entry silicon "Inner tracker"
    ∷ entry coil "Solenoid"
    ∷ entry ecalLit "EM calorimeter"
    ∷ entry hcalLit "Hadronic calorimeter"
    ∷ entry muLit "Muon spectrometer"
    ∷ entry track "Charged track"
    ∷ entry muonColour "Muon"
    ∷ []))
  heading = put 790 90 (vcatA left 4
    ( label 34 "ATLAS" (filled ink defaultStyle)
    ∷ label 15 "simplified" (filled subtle defaultStyle)
    ∷ []))

  -- layers laid over the background, the topmost first
  scene : List (Dia ℕ) → Dia ℕ
  scene ls = canvas (ls ++ background ∷ [])

  -- the detector and the event alone: no title, no legend, no background, and a frame only as
  -- wide as the detector (the legend sits to its right)
  bare : Dia ℕ
  bare = layers 760 H
    ( vertex ∷ muon ++ electron ++ jet ++ photon ++ clusters )

  -- everything
  atlas : Dia ℕ
  atlas = scene
    ( legend ∷ heading ∷ vertex
    ∷ muon ++ electron ++ jet ++ photon
    ++ clusters )

atlasIn : View → Theme → Dia ℕ
atlasIn V T = Parts.atlas T V

atlasBareIn : View → Theme → Dia ℕ
atlasBareIn V T = Parts.bare T V

atlasOn : Theme → Dia ℕ
atlasOn = atlasIn flat

-- the defaults: the dark theme, looking down the beam and a little turned
atlas atlasTurned atlasBare : Dia ℕ
atlas       = atlasOn light
atlasTurned = atlasIn turned light
atlasBare   = atlasBareIn turned light
