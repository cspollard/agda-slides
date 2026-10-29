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
-- Everything is a diagram over whole numbers.  A point of the detector is (r , a , z): a radius,
-- an angle in 1/1024 turns (from the right, growing clockwise on the page, y being downwards)
-- and a position along the beam in hundredths (towards the viewer is positive).  A `View` turns
-- the detector about the vertical axis (`yaw`, which shows its length) and about the line of
-- sight (`roll`, which tilts the picture), and `proj V r a z` is the point on the page, in
-- orthographic projection.  The view `flat` looks down the beam: the cylinder is a set of rings,
-- the transverse plane.  Each layer is drawn as its end face (a ring of cells), the outer
-- surface of the cells that face the viewer, and the walls the cut leaves; the event goes over
-- all of these, as if the detector were transparent.  The sine is `Slides.Examples.LHC`'s table,
-- a little finer in the interpolation.
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
open import Data.Integer using (ℤ; +_) renaming (_+_ to _+ᶻ_; _*_ to _*ᶻ_; _-_ to _-ᶻ_; -_ to negᶻ; ∣_∣ to absᶻ; _≤ᵇ_ to _≤ᶻᵇ_)
open import Data.List using (List; []; _∷_; map; reverse; applyUpTo; concat; foldr; _++_)
open import Data.Nat using (ℕ; suc; _+_; _*_; _∸_; _/_; _%_; _<ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)

open import Slides.Diagram.Convenience
open import Slides.Diagram.Style using (filled; stroked; thick; faded; dashed; anchored)
open import Slides.Examples.LHC using (sinTable; nth)

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

-- (cos , sin) in tenthousandths
sc : ℕ → ℤ × ℤ
sc a = signed (proj₁ t) , signed (proj₂ t)
  where t = trig a
        signed : ℕ × Bool → ℤ
        signed (m , neg) = if neg then negᶻ (+ m) else + m

positive : ℤ → Bool
positive (+ suc _) = true
positive _         = false

------------------------------------------------------------------------
-- Views

-- the turn about the vertical axis and the roll about the line of sight, in 1/1024 turns
record View : Set where
  constructor view
  field
    yaw roll : ℕ

-- looking down the beam, and a little turned (14° and 3°) to show the length
flat turned : View
flat   = view 0 0
turned = view 40 8

-- the point on the page of the point at radius r, angle a, and z in hundredths.  The far end
-- (z negative) moves to the right, so the barrel's outer surface shows on the right.
proj : View → ℕ → ℕ → ℤ → ℕ × ℕ
proj (view yw rl) r a z = fin CX x₂ , fin CY y₂
  where
    c  s  cθ sθ cρ sρ : ℤ
    c  = proj₁ (sc a)
    s  = proj₂ (sc a)
    cθ = proj₁ (sc yw)
    sθ = proj₂ (sc yw)
    cρ = proj₁ (sc rl)
    sρ = proj₂ (sc rl)

    -- the turn about the vertical axis (scaled 10⁸), then the roll (10¹²)
    x₁ y₁ x₂ y₂ : ℤ
    x₁ = (((+ r) *ᶻ c) *ᶻ cθ) -ᶻ ((z *ᶻ + 100) *ᶻ sθ)
    y₁ = ((+ r) *ᶻ s) *ᶻ + 10000
    x₂ = (x₁ *ᶻ cρ) -ᶻ (y₁ *ᶻ sρ)
    y₂ = (x₁ *ᶻ sρ) +ᶻ (y₁ *ᶻ cρ)

    scale : ℕ
    scale = 1000000000000

    -- the centre moved by the scaled offset, to the nearest unit (the offset keeps it positive)
    fin : ℕ → ℤ → ℕ
    fin c₀ v = (absᶻ (v +ᶻ + ((c₀ + 2000) * scale + scale / 2)) / scale) ∸ 2000

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
  open View V using (yaw)

  -- the angles, radii and z of the picture's points
  pt : ℕ → ℕ → ℤ → ℕ × ℕ
  pt = proj V

  end : ℤ
  end = + (half * 100)

  -- the points of the arc at radius r from angle a for w, at z, a point every 8
  arcPts : ℕ → ℕ → ℕ → ℤ → List (ℕ × ℕ)
  arcPts r a w z = map (λ j → pt r (a + 8 * j) z) (applyUpTo (λ j → j) (suc (w / 8)))

  -- the cell between the radii r₀ < r₁, from angle a for w, in the plane z
  cell : ℕ → ℕ → ℕ → ℕ → ℤ → List (ℕ × ℕ)
  cell r₀ r₁ a w z = arcPts r₁ a w z ++ reverse (arcPts r₀ a w z)

  -- the outer surface of a cell over the whole length of the barrel, and a wall at angle a
  patch : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  patch r a w = arcPts r a w (negᶻ end) ++ reverse (arcPts r a w end)

  wall : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  wall r₀ r₁ a = pt r₀ a (negᶻ end) ∷ pt r₁ a (negᶻ end) ∷ pt r₁ a end ∷ pt r₀ a end ∷ []

  -- how far towards the viewer the point (r , a , z) is, to compare: the turn about the vertical
  -- axis takes the point's x to a depth of x times the sine of the yaw
  depth : ℕ → ℕ → ℤ → ℤ
  depth r a z = (((+ r) *ᶻ proj₁ (sc a)) *ᶻ proj₂ (sc yaw)) +ᶻ ((z *ᶻ + 100) *ᶻ proj₁ (sc yaw))

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

  -- a face with the depth of a point in it (r , a , z): a translucent fill with an opaque
  -- outline over it
  Face : Set
  Face = ℤ × List (Dia ℕ)

  face : String → String → ℕ → ℤ → List (ℕ × ℕ) → Face
  face fl rm o d ps = d , ( put 0 0 (polygon ps (paint fl fl 0 o))
                          ∷ put 0 0 (polygon ps (line rm 1)) ∷ [] )

  -- the faces of a cell of a layer, all of them: both end faces, and the surfaces at its two
  -- radii.  The fill is faint enough to see the far side through the near one.
  cellFaces : String → String → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List Face
  cellFaces fl rm o bias r₀ r₁ a w = ends ++ surfaces
    where
      mid rmid : ℕ
      mid  = a + w / 2
      rmid = (r₀ + r₁) / 2
      ends = face fl rm o (depth rmid mid end +ᶻ + bias) (cell r₀ r₁ a w end)
           ∷ face fl rm o (depth rmid mid (negᶻ end) +ᶻ + bias) (cell r₀ r₁ a w (negᶻ end))
           ∷ []
      surfaces = face fl rm o (depth r₁ mid (+ 0) +ᶻ + bias) (patch r₁ a w)
               ∷ (if 0 <ᵇ r₀ then face fl rm o (depth r₀ mid (+ 0) +ᶻ + bias) (patch r₀ a w) ∷ [] else [])

  -- the faces of a layer: its cells, and the walls the cut leaves
  layerFaces : Layer → List Face
  layerFaces L = walls ++ concat (map (λ a → cellFaces fill rim 30 0 r₀ r₁ a w) (starts L))
    where
      open Layer L
      lo : ℕ
      lo = (hi + n * w) % 1024
      wallAt : ℕ → Face
      wallAt a = face fill rim 30 (depth ((r₀ + r₁) / 2) a (+ 0)) (wall r₀ r₁ a)
      walls = if 1024 <ᵇ n * w + 1 then [] else wallAt lo ∷ wallAt hi ∷ []

  -- the faces of the lit cells of a layer, whole volumes: the cell's faces and its two walls.  A
  -- lit face goes a little in front of the quiet one it overlaps.
  litFaces : Layer → List Face
  litFaces L = concat (map volume lits)
    where
      open Layer L
      volume : Lit → List Face
      volume (a , l) = cellFaces litC litC (glow l * 38 / 100) 1 r₀ r₁ a w
        ++ map wallAt (a ∷ a + w ∷ [])
        where wallAt = λ b → face litC litC (glow l * 38 / 100) (depth ((r₀ + r₁) / 2) b (+ 0) +ᶻ + 1) (wall r₀ r₁ b)

  -- insertion sort by depth, the farthest first
  insert : Face → List Face → List Face
  insert p []       = p ∷ []
  insert p (q ∷ qs) = if proj₁ p ≤ᶻᵇ proj₁ q then p ∷ q ∷ qs else q ∷ insert p qs

  sortFaces : List Face → List Face
  sortFaces = foldr insert []

  -- the silicon layers: rings round the end face of the tracker
  silicons : List (Dia ℕ)
  silicons = map (λ r → put 0 0 (polygon (arcPts r 0 1024 end) (faded 70 (thick 1 (stroked silicon defaultStyle))))) (siliconR ++ 100 ∷ [])

  -- the detector: the silicon layers over every face of every layer, the nearest on top.  With the
  -- lit cells, each goes in its place among them, so whatever lies in front of a lit cell (the
  -- tracker, the solenoid, the layers outside) shows over it.
  stack : Bool → List (Dia ℕ)
  stack lit? = silicons ++ concat (map proj₂ (reverse (sortFaces
    (concat (map layerFaces layers′) ++ (if lit? then concat (map litFaces layers′) else [])))))

  -- the quiet cells with their tracker, and the same with the lit cells (the clusters)
  detector clusters : List (Dia ℕ)
  detector = stack false
  clusters = stack true

  ----------------------------------------------------------------------
  -- The particles

  trackPt : ℕ → Bool → ℕ → ℤ → ℕ → ℕ × ℕ
  trackPt φ neg b s r = pt r (bendAt φ neg b r) (s *ᶻ + r)

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
  label size t st = impure (Text 0 (size * 3 / 2) size t (anchored "start" st) , λ ())

  swatch : String → Dia ℕ
  swatch c = disc 6 (paint c c 1 100)

  entry : String → String → Dia ℕ
  entry c l = hcat 12 (swatch c ∷ label 17 l (filled ink defaultStyle) ∷ [])

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
    ( label 34 "ATLAS" (filled ink defaultStyle)
    ∷ label 15 "simplified" (filled subtle defaultStyle)
    ∷ []))

  -- layers laid over the background, the topmost first
  scene : List (Dia ℕ) → Dia ℕ
  scene ls = canvas (ls ++ background ∷ [])

  -- everything
  atlas : Dia ℕ
  atlas = scene
    ( legend ∷ heading ∷ vertex
    ∷ muon ++ electron ++ jet ++ photon
    ++ clusters )

atlasIn : View → Theme → Dia ℕ
atlasIn V T = Parts.atlas T V

atlasOn : Theme → Dia ℕ
atlasOn = atlasIn flat

-- the defaults: the dark theme, looking down the beam and a little turned
atlas atlasTurned : Dia ℕ
atlas       = atlasOn light
atlasTurned = atlasIn turned light
