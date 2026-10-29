{-# OPTIONS --safe --without-K #-}

-- The diagram language: the free monad of the layout signature over a scalar `S`.
--
-- `Op S` is the signature.  *Primitives* have no sub-diagram and an intrinsic size (a frame
-- stored in the node); *connectives* place the frames of their children relative to each other
-- and *annotations* do not change the geometry.  `arity` makes `DiagramC S = Op S ▷ arity` a
-- container, a diagram is a closed program `DiagramC S ⋆ ⊥`, and an interpretation is a
-- `Handler` read by `pfold` (`Slides.Diagram.Layout`, `Names`, `Size`).  The size of a
-- composite is never stored: it is synthesised (`Slides.Diagram.Size`).  A map of scalars acts
-- on a diagram by the container morphism `mapC` (`mapDia`).
--
--   Conventions.  Origin: top-left of a frame; x grows right, y grows DOWN.  A frame is all a
--   neighbour sees.  A connective never scales a child, it shifts it inside a new frame.  Of
--   two children the second is drawn on top.  Sizes are in units, positions in half units
--   (so centring is a difference of sizes, with no division).
--
--     Rectangle w h   Disc r        Segment w h   Text w h     Path w h      Spacer w h
--     +-------+       +-----+       *             +--------+   +-------+     +       +
--     |       | h     | ( ) | 2r    | \           |  text  |   | d ... |
--     +-------+       +-----+       +--*          +--------+   +-------+     +       +
--
--     Ellipse rx ry   Polyline closed pts
--     +---------+     +-----------+   frame: the extent of the points from the origin
--     |  ( _ )  | 2ry |  p2       |   (largest x by largest y, so none is negative; no
--     +---------+     | p1  p3    |   points, the empty frame); drawn as an SVG polyline, or a
--      2rx            +-----------+   fillable polygon when closed.  Scalar-parametric, unlike
--                                     `Path`, whose `d` string is opaque and cannot move
--                                     with scalars or the animation time.
--
--     `Disc r` has the frame and size of `Ellipse r r` (`size-disc-ellipse`); it stays a
--     constructor so that it prints as `<circle>`.
--
--
--     Beside al        Above al      Atop          LabelAbove       Place w h x y  Overlay w h
--     +--+--+          +--+          +----------+  +-----+          +----------+   +-------+
--     |a |b |          |a |          |  +----+  |  | lbl |          |  (x,y)+-+|   | a   b |
--     +--+--+          +--+--+       |  | b  |  |  +-----+          |       |d||   +-------+
--                      | b   |      +----------+  |  d  | (room of  +----------+
--                      +-----+                    +-----+  lbl below)
--
--     Named n d: the frame of d under the name n      Connect a pa b pb d: an arrow a → b over d

module Slides.Diagram.Syntax where

open import Level using (0ℓ)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin)
open import Data.List using (List; map)
open import Data.Nat using (ℕ; _*_; _/_)
open import Data.String using (String)
open import Data.Unit using (⊤)
open import Data.Product.Base using (_×_; _,_)
open import Data.Container.Core using (Container; _▷_; _⇒_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)

open import Container.Pick using (pick2)
open import Container.Lowering using (translate)
open import Slides.Diagram.Style using (Style)
open import Slides.Diagram.Draw using (mapPt)
open import Slides.Diagram.TextMetrics using (inlineWidth)
open import Slides.Text using (Inline; parse)
open import Slides.Diagram.Geometry public

data Op (S : Set) : Set where
  Rectangle Segment : (w h : S) → Style → Op S
  Disc              : (r : S) → Style → Op S
  Ellipse           : (rx ry : S) → Style → Op S
  Polyline          : (closed : Bool) → List (S × S) → Style → Op S   -- points from the frame's top-left
  Text              : (w h : S) (size : ℕ) → List Inline → Style → Op S   -- frame as measured
  Path              : (w h : S) → String → Style → Op S              -- opaque `d` in the frame's units: not scalar-parametric
  Spacer            : (w h : S) → Op S
  Beside            : VAlign → Op S
  Above             : Align → Op S
  Atop LabelAbove LabelBelow : Op S
  Place             : (w h x y : S) → Op S     -- one child at (x, y) of a declared frame
  Overlay           : (w h : S) → Op S         -- two children at the corner of a declared frame
  Named             : String → Op S
  Connect           : String → Port → String → Port → Style → Op S

arity : ∀ {S} → Op S → Set
arity (Rectangle _ _ _)   = ⊥
arity (Segment _ _ _)     = ⊥
arity (Disc _ _)          = ⊥
arity (Ellipse _ _ _)     = ⊥
arity (Polyline _ _ _)    = ⊥
arity (Text _ _ _ _ _)    = ⊥
arity (Path _ _ _ _)      = ⊥
arity (Spacer _ _)        = ⊥
arity (Beside _)          = Fin 2
arity (Above _)           = Fin 2
arity Atop                = Fin 2
arity LabelAbove          = Fin 2
arity LabelBelow          = Fin 2
arity (Place _ _ _ _)     = ⊤
arity (Overlay _ _)       = Fin 2
arity (Named _)           = ⊤
arity (Connect _ _ _ _ _) = ⊤

DiagramC : Set → Container 0ℓ 0ℓ
DiagramC S = Op S ▷ arity

Dia : Set → Set
Dia S = DiagramC S ⋆ ⊥

------------------------------------------------------------------------
-- Change of scalar: the action on maps, a container morphism (same arities)

mapOp : ∀ {S T} → (S → T) → Op S → Op T
mapOp f (Rectangle w h s)       = Rectangle (f w) (f h) s
mapOp f (Segment w h s)         = Segment (f w) (f h) s
mapOp f (Disc r s)              = Disc (f r) s
mapOp f (Ellipse a b s)         = Ellipse (f a) (f b) s
mapOp f (Polyline c ps s)       = Polyline c (map (mapPt f) ps) s
mapOp f (Text w h n t s)        = Text (f w) (f h) n t s
mapOp f (Path w h d s)          = Path (f w) (f h) d s
mapOp f (Spacer w h)            = Spacer (f w) (f h)
mapOp f (Beside al)             = Beside al
mapOp f (Above al)              = Above al
mapOp f Atop                    = Atop
mapOp f LabelAbove              = LabelAbove
mapOp f LabelBelow              = LabelBelow
mapOp f (Place w h x y)         = Place (f w) (f h) (f x) (f y)
mapOp f (Overlay w h)           = Overlay (f w) (f h)
mapOp f (Named n)               = Named n
mapOp f (Connect a pa b pb s)   = Connect a pa b pb s

mapC : ∀ {S T} → (S → T) → DiagramC S ⇒ DiagramC T
mapC f = record { shape = mapOp f ; position = pos }
  where
    pos : ∀ {o} → arity (mapOp f o) → arity o
    pos {Rectangle _ _ _}   p = p
    pos {Segment _ _ _}     p = p
    pos {Disc _ _}          p = p
    pos {Ellipse _ _ _}     p = p
    pos {Polyline _ _ _}    p = p
    pos {Text _ _ _ _ _}    p = p
    pos {Path _ _ _ _}      p = p
    pos {Spacer _ _}        p = p
    pos {Beside _}          p = p
    pos {Above _}           p = p
    pos {Atop}              p = p
    pos {LabelAbove}        p = p
    pos {LabelBelow}        p = p
    pos {Place _ _ _ _}     p = p
    pos {Overlay _ _}       p = p
    pos {Named _}           p = p
    pos {Connect _ _ _ _ _} p = p

mapDia : ∀ {S T} → (S → T) → Dia S → Dia T
mapDia f = translate (mapC f)

------------------------------------------------------------------------
-- The surface language

rectangle segment : ∀ {S} → S → S → Style → Dia S
rectangle w h s = impure (Rectangle w h s , λ ())
segment w h s   = impure (Segment w h s , λ ())

disc : ∀ {S} → S → Style → Dia S
disc r s = impure (Disc r s , λ ())

ellipse : ∀ {S} → S → S → Style → Dia S
ellipse a b s = impure (Ellipse a b s , λ ())

-- through the points (from the top-left corner), open or closed
polyline polygon : ∀ {S} → List (S × S) → Style → Dia S
polyline ps s = impure (Polyline false ps s , λ ())
polygon ps s  = impure (Polyline true ps s , λ ())

spacer : ∀ {S} → S → S → Dia S
spacer w h = impure (Spacer w h , λ ())

path : ∀ {S} → S → S → String → Style → Dia S
path w h d s = impure (Path w h d s , λ ())

-- a line of text at a font size: as wide as its characters times `pct` percent (a heavier
-- font is wider), `size * 3/2` high; `fromℕ` reads a number of units as a length
text : ∀ {S} → (ℕ → S) → (pct size : ℕ) → String → Style → Dia S
text fromℕ pct size t s =
  impure (Text (fromℕ ((inlineWidth size is * pct) / 100)) (fromℕ ((size * 3) / 2)) size is s , λ ())
  where is = parse t

besideA : ∀ {S} → VAlign → Dia S → Dia S → Dia S
besideA al a b = impure (Beside al , pick2 a b)

aboveA : ∀ {S} → Align → Dia S → Dia S → Dia S
aboveA al a b = impure (Above al , pick2 a b)

beside above atop labelAbove labelBelow : ∀ {S} → Dia S → Dia S → Dia S
beside = besideA middle
above  = aboveA centred
atop a b       = impure (Atop , pick2 a b)
labelAbove l d = impure (LabelAbove , pick2 l d)    -- caption, diagram, room of the caption's height
labelBelow l d = impure (LabelBelow , pick2 l d)    -- the diagram is at the centre either way

overlay : ∀ {S} → S → S → Dia S → Dia S → Dia S
overlay w h a b = impure (Overlay w h , pick2 a b)

place : ∀ {S} → S → S → S → S → Dia S → Dia S
place w h x y d = impure (Place w h x y , λ _ → d)

named : ∀ {S} → String → Dia S → Dia S
named n d = impure (Named n , λ _ → d)

connectP : ∀ {S} → String → Port → String → Port → Style → Dia S → Dia S
connectP a pa b pb s d = impure (Connect a pa b pb s , λ _ → d)

connect : ∀ {S} → String → Side → String → Side → Style → Dia S → Dia S
connect a sa b sb = connectP a (side sa) b (side sb)

-- a rectangle with a diagram centred on it
framed : ∀ {S} → S → S → Style → Dia S → Dia S
framed w h s d = atop (rectangle w h s) d
